module POMC.Opa ( Prec(..)
                , Opa(..)
                , run
                ) where

data Prec = Yield | Equal | Take deriving (Eq, Show)

data Opa s t = Opa
    { alphabet   :: [t]
    , prec       :: t -> t -> Prec
    , states     :: [s]
    , initials   :: [s]
    , finals     :: [s]
    , deltaShift :: s -> t -> [s]
    , deltaPush  :: s -> t -> [s]
    , deltaPop   :: s -> s -> [s]
    }

data Config s t = Config
    { confState :: s
    , confStack :: [(t, s)]
    , confInput :: [t]
    } deriving (Show)

run :: (Eq s) => Opa s t -> [t] -> Bool
run (Opa _ prec _ initials finals dshift dpush dpop) ts =
  any
    (run' prec dshift dpush dpop finals)
    (map (\i -> Config i [] ts) initials)

  where
    run' prec dshift dpush dpop fs conf@(Config s stack tokens)
      -- No more input and empty stack: accept / reject
      | null tokens && null stack = s `elem` fs

      -- No more input but stack non empty: pop
      | null tokens = any recurse (pop dpop conf)

      -- Stack empty or stack top yields to next token: push
      | null stack || prec (fst top) t == Yield =
        any recurse (push dpush conf)

      -- Stack top has same precedence as next token: shift
      | prec (fst top) t == Equal =
        any recurse (shift dshift conf)

      -- Stack top takes precedence on next token: pop
      | prec (fst top) t == Take =
        any recurse (pop dpop conf)

      where top = head stack  --
            t   = head tokens -- safe due to laziness
            recurse = run' prec dshift dpush dpop fs

push dpush (Config s stack (t:ts)) =
  map
    (\s' -> (Config s' ((t, s):stack) ts))
    (dpush s t)

shift dshift (Config s stack (t:ts)) =
  map
    (\s' -> (Config s' ((t, (snd (head stack))):(tail stack)) ts))
    (dshift s t)

pop dpop (Config s stack tokens) =
  map
    (\s' -> (Config s' (tail stack) tokens))
    (dpop s (snd (head stack)))
