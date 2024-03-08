{-# LANGUAGE TypeOperators, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances, Rank2Types #-}

module Example.Basic where

import Control.Mp.Eff
import Control.Mp.Util

safediv h x y = if y == 0 then perform throwError h "Division by zero"
                          else return (x/y)

safedivEither x y = exceptEither $ \h -> safediv h x y
safedivMaybe x y = exceptMaybe $ \h -> safediv h x y
safedivDefault x y = exceptDefault 0 $ \h -> safediv h x y