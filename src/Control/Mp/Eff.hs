{-# LANGUAGE  TypeOperators,            -- h :* e                     (looks nice but not required)
              ConstraintKinds,          -- type (h ?: e) = In h e     (looks nice but not required)
              FlexibleInstances,        -- instance Sub () e          (non type variable in head)
              FlexibleContexts,         -- (State Int ?: e) => ...    (non type variable argument)
              DataKinds, TypeFamilies,  -- type family HEqual h h' :: Bool
              UndecidableInstances,     -- InEq (HEqual h h') h h' e => ... (duplicate instance variable)
              ScopedTypeVariables,
              GADTs,
              MultiParamTypeClasses,
              Rank2Types,
              AllowAmbiguousTypes
#-}
{-|
Description : Efficient effect handlers based on Evidence Passing Semantics
Copyright   : (c) 2021, Ningning Xie, Daan Leijen
License     : MIT
Maintainer  : xnning@hku.hk; daan@microsoft.com
Stability   : Experimental

Efficient effect handlers based on Evidence passing semantics. The implementation
is based on /"Generalized Evidence Passing for Effect Handlers"/, Ningning Xie and Daan Leijen, 2021 [(pdf)](https://www.microsoft.com/en-us/research/publication/generalized-evidence-passing-for-effect-handlers/),
The implementation is closely based on the [Ev.Eff](https://hackage.haskell.org/package/eveff) 
library described in detail in /"Effect Handlers in Haskell, Evidently"/, Ningning Xie and Daan Leijen, Haskell 2020 [(pdf)](https://www.microsoft.com/en-us/research/publication/effect-handlers-in-haskell-evidently).
The _Mp.Eff_ and _Ev.Eff_ libraries expose the exact same interface, but
the _Mp.Eff_ library can express full effect handler semantics, including non-scoped resumptions --
it is slightly slower though (see the 2021 paper for benchmarks and a detailed comparison).

An example of defining and using a @Reader@ effect:

@
\{\-\# LANGUAGE  TypeOperators, FlexibleContexts, Rank2Types  \#\-\}
import Control.Mp.Eff

-- A @Reader@ effect definition with one operation @ask@ of type @()@ to @a@.
data Reader a e ans = Reader{ ask :: `Op` () a e ans }

greet :: (Reader String `:?` e) => `Eff` e String
greet = do s <- `perform` ask ()
           return ("hello " ++ s)

test :: String
test = `runEff` $
       `handler` (Reader{ ask = `value` "world" }) $  -- @:: Reader String () Int@
       do s <- greet                              -- executes in context @:: `Eff` (Reader String `:*` ()) Int@
          return (length s)
@

Enjoy,

Ningning Xie and Daan Leijen,  Mar 2021.

-}
module Control.Mp.Eff(
            -- * Effect monad
              Eff
            , runEff          -- :: Eff () a -> a

            -- * Effect context
            -- , (:?)            -- h :? e,  is h in e?
            , In 
            , (:*)            -- h :* e,  cons h in front of e
            , (:@)
            -- , In           -- alias for :?

            , Ev

            -- * Perform and Handlers
            , perform         -- :: (h :? e) => (forall e' ans. h e' ans -> Op a b e' ans) -> a -> Eff e b
            , handler         -- :: h e ans -> Eff (h :* e) ans -> Eff e ans
            , handlerRet      -- :: (ans -> b) -> h e b -> Eff (h :* e) ans -> Eff e b
            , handlerHide     -- :: h (h' :* e) ans -> Eff (h :* e) ans -> Eff (h' :* e) ans
            , mask            -- :: Eff e ans -> Eff (h :* e) ans

            -- * Defining operations
            , Op
            , value           -- :: a -> Op () a e ans
            , function        -- :: (a -> Eff e b) -> Op a b e ans
            , except          -- :: (a -> Eff e ans) -> Op a b e ans
            , operation       -- :: (a -> (b -> Eff e ans)) -> Op a b e ans

            -- * Local state
            , Local           -- Local a e ans

            , local           -- :: a -> Eff (Local a :* e) ans -> Eff e ans
            , localRet        -- :: a -> (ans -> a -> b) -> Eff (Local a :* e) ans -> Eff e b
            , handlerLocal    -- :: a -> h (Local a :* e) ans -> Eff (h :* e) ans -> Eff e ans
            , handlerLocalRet -- :: a -> (ans -> a -> b) -> h (Local a :* e) b -> Eff (h :* e) ans -> Eff e b

            , lget            -- :: (Local a :? e) => Eff e a
            , lput            -- :: (Local a :? e) => a -> Eff e ()
            , lmodify         -- :: (Local a :? e) => (a -> a) -> Eff e ()

            , localGet        -- :: Eff (Local a :* e) a
            , localPut        -- :: a -> Eff (Local a :* e) ()
            , localModify     -- :: (a -> a) -> Eff (Local a :* e) a

            ) where

import Prelude hiding (read,flip)
import Control.Monad( ap, liftM )
import Data.Type.Equality( (:~:)( Refl ) )
import Control.Monad.Primitive

-------------------------------------------------------
-- Assume some way to generate a fresh prompt marker
-- associated with specific effect and answer type.
-------------------------------------------------------
import Unsafe.Coerce     (unsafeCoerce)
import System.IO.Unsafe ( unsafePerformIO )
import Data.IORef

-- an abstract marker
data Marker (h:: * -> * -> *) e a = Marker !Integer

infixr 5 :@

data Un (h :: * -> * -> *)
data (h :: * -> * -> *) :@ s

data Ev (h :: * -> * -> *) s e a = Ev (Marker h e a) (h e a) (Context e)
data EvU (h :: * -> * -> *) e a = EvU (Marker h e a) (h e a) (Context e)

instance Show (Marker h e a) where
  show (Marker i) = show i

-- if markers match, their types are the same
mmatch :: Marker h e a -> Marker h' e' b -> Maybe ((h e a, a, e) :~: (h' e' b, b, e'))
mmatch (Marker i) (Marker j) | i == j  = Just (unsafeCoerce Refl)
mmatch _ _ = Nothing

{-# NOINLINE unique #-}
unique :: IORef Integer
unique = unsafePerformIO (newIORef 0)

-- evaluate a action with a fresh marker
{-# NOINLINE freshMarker #-}
freshMarker :: (Marker h e a -> Eff e a) -> Eff e a
freshMarker f
  = let m = unsafePerformIO $
            do i <- readIORef unique;
               writeIORef unique (i+1);
               return i
    in seq m (f (Marker m))

-------------------------------------------------------
-- The handler context
-------------------------------------------------------
infixr 5 :*

data hs :* e

data Context e where
  CCons :: !(Ev h s e' ans) -> !(ContextT e e') -> !(Context e) -> Context ((h:@s) :* e)
  CConsU :: !(EvU h e' ans) -> !(ContextT e e') -> !(Context e) -> Context (Un h :* e)
  CNil  :: Context ()

data ContextT e e' where
  CTCons :: !(Ev h s e' ans) -> !(ContextT e e') -> ContextT e ((h:@s) :* e)
  CTConsU :: !(EvU h e' ans) -> !(ContextT e e') -> ContextT e (Un h :* e)
  CTId   :: ContextT e e
  -- CTComp :: ContextT e'' e' -> ContextT e e'' -> ContextT e e'
  -- CTFun :: !(Context e -> Context e') -> ContextT e e'

-- apply a context transformer
applyT :: ContextT e e' -> Context e -> Context e'
applyT (CTCons ev g) ctx = CCons ev g ctx
applyT (CTId) ctx         = ctx
--applyT (CTComp c1 c2) ctx = applyT c1 (applyT c2 ctx)
--applyT (CTFun f) ctx = f ctx

-- the tail of a context
ctail :: Context (h :* e) -> Context e
ctail (CCons _ _ ctx)   = ctx

-------------------------------------------------------
-- The Multi Prompt control monad
-- ans: the answer type, i.e. the type of the handler/prompt context.
-- e' : the answer effect, i.e. the effect in the handler/prompt context.
-- b  : the result type of the operation
-------------------------------------------------------
data Ctl e a = Pure { result :: !a }
             | forall h b e' s ans.
               Control{ ev     :: Ev h s e' ans,                       -- prompt marker to yield to (in type context `::ans`)
                        op     :: !((b -> Eff e' ans) -> Eff e' ans),  -- the final action, just needs the resumption (:: b -> Eff e' ans) to be evaluated.
                        cont   :: !(b -> Eff e a) }                    -- the (partially) build up resumption; (b -> Eff e a) :~: (b -> Eff e' ans)` by the time we reach the prompt


newtype Eff e a = Eff { unEff :: Context e -> Ctl e a }

{-# INLINE lift #-}
lift :: Ctl e a -> Eff e a
lift ctl = Eff (\ctx -> ctl)

{-# INLINE ctxMap #-}
ctxMap :: (Context e' -> Context e) -> Eff e a -> Eff e' a
ctxMap f eff = Eff (\ctx -> ctxMapCtl f $ unEff eff (f ctx))

ctxMap2 f action = Eff (\ctx -> ctxMapCtl f $ unEff (action ctx) (f ctx))

{-# INLINE ctxMapCtl #-}
ctxMapCtl :: (Context e' -> Context e) -> Ctl e a -> Ctl e' a
ctxMapCtl f (Pure x) = Pure x
ctxMapCtl f (Control m op cont) = Control m op (\b -> ctxMap f (cont b))

{-# INLINE hideSecond #-}
hideSecond :: Eff ((h :@ s) :* e) a -> Eff ((h :@ s) :* (h' :@ s') :* e) a
hideSecond eff = ctxMap (\(CCons ev CTId (CCons ev' g' ctx)) ->
                             CCons ev (CTCons ev' g') ctx) eff

under :: In (h :@ s) e => Ev h s e' ans -> Eff e' b -> Eff e b
-- under m ctx (Eff eff) = Eff (\_ -> case eff ctx of
--                                        Pure x -> Pure x
--                                        Control n op cont -> Control n op (resumeUnder m ctx cont))

under ev@(Ev m h ctx) (Eff eff) = Eff (\_ -> case eff ctx of
                                              Pure x -> Pure x
                                              Control n op cont -> Control n op (resumeUnder ev cont))

resumeUnder :: forall h s a b e e' ans. In (h :@ s) e => Ev h s e' ans -> (b -> Eff e' a) -> (b -> Eff e a)
resumeUnder ev@(Ev m h ctx) cont x = under ev (cont x)
-- resumeUnder ev = ((.) . (.)) under ev ($)
-- resumeUnder ev@(Ev m h (CCons ev'@(Ev m' h' _) g' ctx')) cont x
--   = case mmatch m m' of
--       Just Refl -> under (Ev m h (applyT g' ctx')) (cont x)
--       Nothing   -> error "EffEv.resumeUnder: marker does not match anymore (this should never happen?)"


instance Functor (Eff e) where
  fmap  = liftM
instance Applicative (Eff e) where
  pure  = return
  (<*>) = ap
instance Monad (Eff e) where
  return x   = Eff (\evv -> Pure x)
  (>>=)      = bind

-- start yielding (with an initially empty continuation)
{-# INLINE yield #-}
yield :: Ev h s e ans -> ((b -> Eff e ans) -> Eff e ans) -> Eff e' b
yield m op  = Eff (\ctx -> Control m op pure)

{-# INLINE kcompose #-}
kcompose :: (b -> Eff e c) -> (a -> Eff e b) -> a -> Eff e c      -- Kleisli composition
kcompose g f x =
  case f x of
    -- bind (f x) g
    Eff eff -> Eff (\ctx -> case eff ctx of
                              Pure x -> unEff (g x) ctx
                              Control m op cont -> Control m op (g `kcompose` cont))

{-# INLINE bind #-}
bind :: Eff e a -> (a -> Eff e b) -> Eff e b
bind (Eff eff) f
  = Eff (\ctx -> case eff ctx of
                   Pure x            -> unEff (f x) ctx
                   Control m op cont -> Control m op (f `kcompose` cont))  -- keep yielding with an extended continuation

instance Functor (Ctl e) where
  fmap  = liftM
instance Applicative (Ctl e) where
  pure  = return
  (<*>) = ap
instance Monad (Ctl e) where
  return x      = Pure x
  Pure x >>= f  = f x
  (Control m op cont) >>= f
    = Control m op (f `kcompose2` cont)

kcompose2 :: (b -> Ctl e c) -> (a -> Eff e b) -> a -> Eff e c
kcompose2 g f x
  = Eff $ \ctx -> case unEff (f x) ctx of
        Pure x -> g x
        Control m op cont -> Control m op (g `kcompose2` cont)


-- use a prompt with a unique marker (and handle yields to it)
{-# INLINE prompt #-}
prompt :: Marker h e ans -> h e ans -> (Ev h s e ans -> Eff ((h :@ s) :* e) ans) -> Eff e ans
prompt m h action = Eff $ \ctx ->
  case (unEff (action (Ev m h ctx)) (CCons (Ev m h ctx) CTId ctx)) of                    -- add handler to the context
    Pure x -> Pure x
    Control ev@(Ev n h' ctx') op cont ->
        let cont' x = prompt m h (\_ -> cont x) in      -- extend the continuation with our own prompt
        case mmatch m n of
          Nothing   -> Control ev op cont'          -- keep yielding (but with the extended continuation)
          Just Refl -> unEff (op cont') ctx   -- found our prompt, invoke `op` (under the context `ctx`).
                              -- Note: `Refl` proves `a ~ ans` and `e ~ e'` (the existential `ans,e'` in Control)

{-# INLINE handler #-}
handler :: h e ans -> (forall s. Ev h s e ans -> Eff ((h :@ s) :* e) ans) -> Eff e ans
handler h action
  = freshMarker $ \m -> prompt m h action

-- Run a control monad
runEff :: Eff () a -> a
runEff (Eff eff) = case eff CNil of
                   Pure x -> x
                   Control _ _ _ -> error "Unhandled operation"  -- can never happen

{-# INLINE handlerRet #-}
handlerRet :: (ans -> a) -> h e a -> (forall s. Ev h s e a -> Eff ((h :@ s) :* e) ans) -> Eff e a
handlerRet ret h action
  = handler h (\ev -> do x <- (action ev); return (ret x))

{-# INLINE handlerHide #-}
handlerHide :: h ((h' :@ s') :* e) ans -> (forall s. Ev h s ((h' :@ s') :* e) ans -> Eff ((h :@ s) :* e) ans) -> Eff ((h' :@ s') :* e) ans
handlerHide h action
  = handler h (\ev -> (hideSecond $ action ev))

{-# INLINE handlerHideRetEff #-}
handlerHideRetEff :: (ans -> Eff ((h' :@ s') :* e) b) -> h ((h' :@ s') :* e) b -> (forall s. Ev h s ((h' :@ s') :* e) b -> Eff ((h :@ s) :* e) ans) -> Eff ((h' :@ s') :* e) b
handlerHideRetEff ret h action
  = handler h (\ev -> do x <- hideSecond (action ev); mask (ret x))

-- | Mask the top effect handler in the give action (i.e. if a operation is performed
-- on an @h@ effect inside @e@ the top handler is ignored).
mask :: forall h s e ans. Eff e ans -> Eff ((h :@ s) :* e) ans
mask eff = ctxMap ctail eff

---------------------------------------------------------
--
---------------------------------------------------------

-- type h :? e = In h s e

data SubContext h = forall h e. SubContext !(Context (h :* e))

-- type In h se = In h se 
class In h e where
  subContext :: Context e -> SubContext h

-- In constraints for named handlers
instance (InEq (HEqual (h :: * -> * -> *) s (h' :: * -> * -> *) s') h s h' s' ctx) => In (h :@ s) ((h' :@ s') :* ctx)  where
  subContext = subContextEq

type family HEqual (h :: * -> * -> *) s (h' :: * -> * -> *) s' :: Bool where
  HEqual h s h s   = 'True
  HEqual h s h' s' = 'False

class (iseq ~ HEqual (h :: * -> * -> *) s (h' :: * -> * -> *) s') => InEq iseq h s h' s' e  where
  subContextEq :: Context ((h' :@ s') :* e) -> SubContext (h :@ s)

instance (h ~ h', s ~ s') => InEq 'True h s h' s' e where
  subContextEq ctx = SubContext ctx

instance ('False ~ HEqual h s h' s', In (h :@ s) e) => InEq 'False h s h' s' e where
  subContextEq ctx = subContext (ctail ctx)




-- {-# INLINE withSubContext #-}
-- withSubContext :: In h s e => (SubContext h s -> Eff e a) -> Eff e a
-- withSubContext action
--   = do ctx <- Eff Pure
--        action (subContext ctx)


------------------------------------
-- Operations
-------------------------------------

-- | The abstract type of operations of type @a@ to @b@, for a handler
-- defined in an effect context @e@ and answer type @ans@.
data Op a b e ans = Op { applyOp:: !(forall h s e'. In (h :@ s) e' => Ev h s e ans -> a -> Eff e' b) }


-- Given evidence and an operation selector, perform the operation
{-# INLINE perform #-}
-- perform :: In h e => Marker h e' ans' -> (forall e' ans. h e' ans -> Op a b e' ans) -> a -> Eff e b
-- perform a selectOp x
--   = withSubContext $ \(SubContext (CCons b h g ctx)) ->
--       case mmatch a b of
--         Just Refl  -> applyOp (selectOp h) b (applyT g ctx) x
--         Nothing -> error "what to do here"

perform :: In (h :@ s) e => (forall e' ans. h e' ans -> Op a b e' ans) -> Ev h s e' ans -> a -> Eff e b
perform selectOp ev@(Ev m h ctx) x = applyOp (selectOp h) ev x

-- | Create an operation that always resumes with a constant value (of type @a@).
-- (see also the `perform` example).
value :: a -> Op () a e ans
value x = function (\() -> return x)

-- | Create an operation that takes an argument of type @a@ and always resumes with a result of type @b@.
-- These are called /tail-resumptive/ operations and are implemented more efficient than
-- general operations as they can execute /in-place/ (instead of yielding to the handler).
-- Most operations are tail-resumptive. (See also the `handlerLocal` example).
function :: (a -> Eff e b) -> Op a b e ans
function f = Op (\m x -> under m (f x))

-- | Create an fully general operation from type @a@ to @b@.
-- the function @f@ takes the argument, and a /resumption/ function of type @b -> `Eff` e ans@
-- that can be called to resume from the original call site. For example:
--
-- @
-- data Amb e ans = Amb { flip :: forall b. `Op` () Bool e ans }
--
-- xor :: (Amb `:?` e) => `Eff` e Bool
-- xor = do x <- `perform` flip ()
--          y <- `perform` flip ()
--          return ((x && not y) || (not x && y))
--
-- solutions :: `Eff` (Amb `:*` e) a -> `Eff` e [a]
-- solutions = `handlerRet` (\\x -> [x]) $
--             Amb{ flip = `operation` (\\() k -> do{ xs <- k True; ys <- k False; return (xs ++ ys)) }) }
-- @
operation :: (a -> (b -> Eff e ans) -> Eff e ans) -> Op a b e ans
operation f = Op (\ev x -> yield ev (\ctlk -> f x ctlk))


-- | Create an operation that never resumes (an exception).
-- (See `handlerRet` for an example).
except :: (a -> Eff e ans) -> Op a b e ans
except f = Op (\ev x -> yield ev (\ctlk -> f x))

--------------------------------------------------------------------------------
-- Efficient (and safe) Local state handler
--------------------------------------------------------------------------------
-- | The type of the built-in state effect.
-- (This state is generally more efficient than rolling your own and usually
-- used in combination with `handlerLocal` to provide local isolated state)
newtype Local a e ans = Local (IORef a)

-- | Unsafe `IO` in the `Eff` monad.
{-# INLINE unsafeIO #-}
unsafeIO :: IO a -> Eff e a
unsafeIO io = let x = unsafeInlinePrim io in seq x (Eff $ \_ -> Pure x)

-- | Get the value of the local state.
{-# INLINE lget #-}
lget :: Local a e ans -> Op () a e ans
lget (Local r) = Op (\m x -> unsafeIO (seq x $ readIORef r))

-- | Set the value of the local state.
{-# INLINE lput #-}
lput :: Local a e ans -> Op a () e ans
lput (Local r) = Op (\m x -> unsafeIO (writeIORef r x))

-- | Update the value of the local state.
{-# INLINE lmodify #-}
lmodify :: Local a e ans -> Op (a -> a) () e ans
lmodify (Local r) = Op (\m f -> unsafeIO (do{ x <- readIORef r; writeIORef r $! (f x) }))

-- | Get the value of the local state if it is the top handler.
localGet :: Ev (Local a) s e ans -> Eff ((Local a :@ s) :* e) a
localGet m = perform lget m ()

-- | Set the value of the local state if it is the top handler.
localPut :: Ev (Local a) s e ans -> a -> Eff ((Local a :@ s) :* e) ()
localPut m x = perform lput m x

-- | Update the value of the local state if it is the top handler.
localModify :: Ev (Local a) s e ans -> (a -> a) -> Eff ((Local a :@ s) :* e) ()
localModify m f = perform lmodify m f

-- A special prompt that saves and restores state per resumption
mpromptIORef :: IORef a -> Eff e b -> Eff e b
mpromptIORef r action
  = Eff $ \ctx -> case (unEff action ctx) of
      p@(Pure _) -> p
      Control m op cont
        -> do val <- unEff (unsafeIO (readIORef r)) ctx                     -- save current value on yielding
              let cont' x = do unsafeIO (writeIORef r val)  -- restore saved value on resume
                               mpromptIORef r (cont x)
              Control m op cont'

-- | Create an `IORef` connected to a prompt. The value of
-- the `IORef` is saved and restored through resumptions.
unsafePromptIORef :: a -> (Marker h e b -> IORef a -> Eff e b) -> Eff e b
unsafePromptIORef init action
  = freshMarker $ \m ->
    do r <- unsafeIO (newIORef init)
       mpromptIORef r (action m r)

-- -- | Create a local state handler with an initial state of type @a@,
-- -- with a return function to combine the final result with the final state to a value of type @b@.
{-# INLINE localRet #-}
localRet :: a -> (ans -> a -> b) -> (forall s. Ev (Local a) s e b -> Eff ((Local a :@ s) :* e) ans) -> Eff e b
localRet init ret action
  = unsafePromptIORef init $ \m r ->  -- set a fresh prompt with marker `m`
        do x <- ctxMap2 (\ctx -> CCons (Ev m (Local r) ctx) CTId ctx) (\ctx -> (action (Ev m (Local r) ctx))) -- and call action with the extra evidence
           y <- unsafeIO (readIORef r)
           return (ret x y)

-- -- | Create a local state handler with an initial state of type @a@.
{-# INLINE local #-}
local :: a -> (forall s. Ev (Local a) s e ans -> Eff ((Local a :@ s) :* e) ans) -> Eff e ans
local init action
  = localRet init const action

-- -- | Create a new handler for @h@ which can access the /locally isolated state/ @`Local` a@.
-- -- This is fully local to the handler @h@ only and not visible in the @action@ as
-- -- apparent from its effect context (which does /not/ contain @`Local` a@). The
-- -- @ret@ argument can be used to transform the final result combined with the final state.
{-# INLINE handlerLocalRet #-}
handlerLocalRet :: a -> (ans -> a -> b) -> (forall s. Ev (Local a) s e b -> h ((Local a :@ s) :* e) b) -> (forall s s'. Ev h s' ((Local a :@ s) :* e) b -> Eff ((h :@ s') :* e) ans) -> Eff e b
handlerLocalRet init ret h action
  = local init $ \ev -> handlerHideRetEff (\x -> do{ y <- localGet ev; return (ret x y)}) (h ev) action

-- -- -- | Create a new handler for @h@ which can access the /locally isolated state/ @`Local` a@.
-- -- -- This is fully local to the handler @h@ only and not visible in the @action@ as
-- -- -- apparent from its effect context (which does /not/ contain @`Local` a@).

-- -- @
-- -- data State a e ans = State { get :: `Op` () a e ans, put :: `Op` a () e ans  }

-- -- state :: a -> `Eff` (State a `:*` e) ans -> `Eff` e ans
-- -- state init = `handlerLocal` init (State{ get = `function` (\\_ -> `perform` `lget` ()),
-- --                                        put = `function` (\\x -> `perform` `lput` x) })

-- -- test = `runEff` $
-- --        state (41::Int) $
-- --        inc                -- see `:?`
-- -- @
{-# INLINE handlerLocal #-}
handlerLocal :: a -> (forall s'. Ev (Local a) s' e ans -> h ((Local a :@ s') :* e) ans) -> (forall s' s. Ev h s ((Local a :@ s') :* e) ans -> Eff ((h :@ s) :* e) ans) -> Eff e ans
handlerLocal init h action = local init (\ev -> handlerHide (h ev) action)
