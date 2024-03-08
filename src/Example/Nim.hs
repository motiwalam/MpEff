{-# LANGUAGE TypeOperators, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances, Rank2Types #-}

module Example.Nim where


import Control.Monad

import Control.Mp.Eff
import Control.Mp.Util

data Player = Alice | Bob
    deriving (Eq, Show)

data NimMove e a = NimMove { move :: Op (Player, Int) Int e a }

alice_turn n g = if n <= 0 then return Bob else do x <- perform move g (Alice, n)
                                                   bob_turn (n - x) g
bob_turn n g = if n <= 0 then return Alice else do x <- perform move g (Bob, n)
                                                   alice_turn (n - x) g
nim_game n g = alice_turn n g

perfect = handler (NimMove { move = function (\(p, n) -> return $ max 1 (n `mod` 4)) })

perfect_game n = perfect $ \g -> nim_game n g

data GameTree = Winner Player | Take Player [(Int, GameTree)]
    deriving Eq

show_gametree indent (Winner p) = show p ++ " wins!"
show_gametree indent (Take p moves) = let lines = map (\(sticks, gtx) -> "\n" ++ take indent (repeat ' ') ++ show sticks ++ " -> " ++ show_gametree (indent + 2) gtx) moves
                                      in show p ++ join lines
instance Show GameTree where
    show = show_gametree 2
    
valid_moves n = filter (<= n) [1,2,3]
gametree = handlerRet Winner $ NimMove { move = operation (\(p,n) k -> let moves = valid_moves n 
                                                                        in do subgames <- mapM k moves
                                                                              return $ Take p (zip moves subgames))}

make_gametree n = gametree $ \g -> nim_game n g