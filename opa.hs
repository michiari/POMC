data Prec = Yp | Ep | Tp deriving (Eq, Show)

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
      | null stack || prec (fst top) t == Yp =
        any recurse (push dpush conf)

      -- Stack top has same precedence as next token: shift
      | prec (fst top) t == Ep =
        any recurse (shift dshift conf)

      -- Stack top takes precedence on next token: pop
      | prec (fst top) t == Tp =
        any recurse (pop dpop conf)

      where top = head stack  --
            t   = head tokens -- safe due to laziness
            recurse = run' prec dshift dpush dpop fs

push dpush (Config s stack (t:ts)) =
  map (\s' -> (Config s' ((t, s):stack) ts)) (dpush s t)

shift dshift (Config s stack (t:ts)) =
  map (\s' -> (Config s' ((t, (snd (head stack))):(tail stack)) ts)) (dshift s t)

pop dpop (Config s stack tokens) =
  map (\s' -> (Config s' (tail stack) tokens)) (dpop s (snd (head stack)))

unsafeLookup :: Eq a => a -> [(a, b)] -> b
unsafeLookup k al = case lookup k al of
  Just v -> v
  Nothing -> error "Failed lookup!"

lookupOrDefault :: Eq a => a -> [(a,b)] -> b -> b
lookupOrDefault k al d = case lookup k al of
  Just v -> v
  Nothing -> d

arithOpaPrecMatrix =
  [ (('+', '+'), Tp)
  , (('+', 'x'), Yp)
  , (('+', '('), Yp)
  , (('+', ')'), Tp)
  , (('+', 'n'), Yp)

  , (('x', '+'), Tp)
  , (('x', 'x'), Tp)
  , (('x', '('), Yp)
  , (('x', ')'), Tp)
  , (('x', 'n'), Yp)

  , (('(', '+'), Yp)
  , (('(', 'x'), Yp)
  , (('(', '('), Yp)
  , (('(', ')'), Ep)
  , (('(', 'n'), Yp)

  , ((')', '+'), Tp)
  , ((')', 'x'), Tp)
  , ((')', '('), Ep) -- not needed
  , ((')', ')'), Tp)
  , ((')', 'n'), Ep) -- not needed

  , (('n', '+'), Tp)
  , (('n', 'x'), Tp)
  , (('n', '('), Ep) -- not needed
  , (('n', ')'), Tp)
  , (('n', 'n'), Ep) -- not needed
  ]

arithOpaDeltaShift = [((3, ')'), [3])]

arithOpaDeltaPush =
  [ ((0, 'n'), [1])
  , ((0, '('), [2])

  , ((1, '+'), [0])
  , ((1, 'x'), [0])

  , ((2, '('), [2])
  , ((2, 'n'), [3])

  , ((3, '+'), [2])
  , ((3, 'x'), [2])
  ]

arithOpaDeltaPop =
  [ ((1, 0), [1])
  , ((1, 1), [1])

  , ((3, 0), [3])
  , ((3, 1), [3])
  , ((3, 2), [3])
  , ((3, 3), [3])
  ]

arithOpa :: Opa Int Char
arithOpa = Opa
  "+xn()"
  (\t1 t2 -> unsafeLookup (t1, t2) arithOpaPrecMatrix)
  [0, 1, 2, 3]
  [0]
  [1, 3]
  (\s  t  -> lookupOrDefault (s,  t)  arithOpaDeltaShift [])
  (\s  t  -> lookupOrDefault (s,  t)  arithOpaDeltaPush  [])
  (\s1 s2 -> lookupOrDefault (s1, s2) arithOpaDeltaPop   [])
