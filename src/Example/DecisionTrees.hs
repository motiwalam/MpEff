{-# LANGUAGE TypeOperators, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances, Rank2Types #-}

module Example.DecisionTrees where

import Control.Mp.Eff
import Control.Mp.Util


type Sequence m = Integer -> m Bool
type Decider m a = Sequence m -> m a
-- Answer a ~ return with answer of type a
-- Question n f t ~ ask for Bit n, do f branch if its false and t branch otherwise
data DTree a = Answer a | Question Integer (DTree a) (DTree a)
    deriving (Eq, Show)
    
tree_to_fun :: Monad m => DTree a -> Decider m a
tree_to_fun (Answer a)       _   = return a
tree_to_fun (Question n f t) seq = do b <- seq n
                                      if b then
                                        tree_to_fun t seq
                                      else
                                        tree_to_fun f seq


data Spy e a = Spy { report :: Op Integer Bool e a }

spy ev n = perform report ev n
command = handlerRet Answer $ Spy {
                report = operation $ \n k -> 
                            do f <- k False
                               t <- k True
                               return $ Question n f t
            }
fun_to_tree :: (forall e. Decider (Eff e) a) -> DTree a
fun_to_tree f = runEff $ command $ \ev -> f (spy ev)

example = fun_to_tree $ \seq -> 
    do a <- seq 2
       b <- seq 3
       c <- seq 5
       d <- seq 7
       e <- seq 11
       return $ (a && b) || (c && d) || e

-- fun_to_tree :: ((Integer -> Bool) -> a) -> DTree a
-- fun_to_tree f = runEff $ command $ \ev -> f (\n -> runEff $ spy ev n)