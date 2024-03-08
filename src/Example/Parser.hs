{-# LANGUAGE TypeOperators, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances, Rank2Types #-}

module Example.Parser where


import Prelude hiding (flip, fail)

import Control.Monad hiding (fail)
import Control.Mp.Eff
import Control.Mp.Util

import Data.Char

data Many a e ans = Many { fail :: Op () a e ans, flip :: Op () Bool e ans }

select h [] = perform fail h ()
select h (x:xs) = do b <- perform flip h ()
                     if b then return x else select h xs


solutions = handlerRet (\x -> [x]) $ Many { fail = value [], flip = operation (\_ k -> do tb <- k True; fb <- k False; return $ tb ++ fb) }
eager = handlerRet (\x -> [x]) $ Many { fail = value [], flip = operation (\_ k -> do tb <- k True
                                                                                      case tb of
                                                                                        [] -> k False
                                                                                        xs -> return xs ) }

choice h p1 p2 = do b <- perform flip h ()
                    if b then p1 h else p2 h

many h p = choice h (\h -> many1 h p) (\h -> return [])
many1 h p = do x <- p h; xs <- many h p; return (x:xs)

data Parse a e ans = Parse { satisfy :: Op (String -> Maybe (a, String)) a e ans }

-- parse :: Many a e ans -> String -> (forall s. Ev (Parse a) s e ans -> Eff ((Parse a :@ s) :* e) ans) -> Eff ((Many a :@ s') :* e) ans
-- parse :: Ev (Many a) s e' ans -> String -> (forall s2. Ev (Parse a) s2 ((Local String :@ s1) :* e) (a1, String) -> Eff ((Parse a :@ s2) :* ((Local String :@ s1) :* e)) (a1, String))
parse h inp = handlerLocalRet inp (,) (\state ->
                    Parse {satisfy = function $ \pred ->
                                        do input <- localGet state
                                           case pred input of
                                            Nothing -> perform fail h ()
                                            Just (res, rest) -> do localPut state rest
                                                                   return res })

char h p = perform satisfy h pred where
            pred [] = Nothing
            pred (x:xs) = if p x then Just (x, xs) else Nothing

symbol h c = char h (== c)

digit h = do c <- char h isDigit
             return $ digitToInt c

number h h1 = do ds <- many1 h (\_ -> digit h1)
                 return $ foldl (\n d -> 10*n + d) 0 ds

expr hmany hparse = choice hmany (\hmany -> 
                do i <- term hmany hparse
                   symbol hparse '+'
                   j <- term hmany hparse
                   return $ i + j)
                          (\hmany -> term hmany hparse)

term hmany hparse = choice hmany (\hmany -> 
                do i <- factor hmany hparse
                   symbol hparse '*'
                   j <- factor hmany hparse
                   return $ i + j)
                          (\hmany -> factor hmany hparse)

factor hmany hparse = choice hmany (\hmany -> number hmany hparse)
                                   (\hmany -> 
                                        do symbol hparse '('
                                           i <- expr hmany hparse
                                           symbol hparse ')'
                                           return i)

-- mparse :: (In (Many a) s1 e, In (Parse Char) s2 e) => (Ev (Many a) s1 e'1 ans1 -> Ev (Parse Char) s2 e'2 ans2 -> Eff e Int
-- mparse :: (Ev (Many a) s e a -> Ev (Parse [(Int, String)]) s' e' a' -> Eff e'' Int) -> Eff e Int

-- mparse:: (forall s s'. Ev (Many [a0]) s e [(a, String)]
--              -> Ev
--                   (Parse [a0])
--                   s'
--                   ((Local String :@ s1) :* ((Many [a0] :@ s) :* e))
--                   (a, String)
--              -> Eff ((Parse [a0] :@ s') :* ((Many [a0] :@ s) :* e)) a) -> String -> Eff e Int
-- mparse p input = solutions $ \hmany -> parse hmany input $ \hparse -> p hmany hparse
-- eparse p input = eager     $ \hmany -> parse hmany input $ \hparse -> p hmany hparse