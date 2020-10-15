data Colour = Red | Black

data RB : Type -> Colour -> Nat -> Type where
  RBNil : RB a Black 0
  BNode : RB a c1 h -> a -> RB a c2 h -> RB a Black (S h)
  RNode : RB a Black h -> a -> RB a Black h -> RB a Red h

total
incrementIfBlack : Colour -> Nat -> Nat
incrementIfBlack Black h = S h
incrementIfBlack Red h = h

total
leaf : (c:Colour) -> a -> RB a c (incrementIfBlack c 0)
leaf Black a = BNode RBNil a RBNil
leaf Red a = RNode RBNil a RBNil

data UnbalRB : Type -> Colour -> Nat -> Type where
  BalRB : RB a c h -> UnbalRB a c h
  RRLeft : RB a Red h -> a -> RB a Black h -> UnbalRB a Red h
  RRRight : RB a Black h -> a -> RB a Red h -> UnbalRB a Red h
  BLeft : UnbalRB a c1 h -> a -> RB a c2 h -> UnbalRB a Black (S h)
  BRight : RB a c1 h -> a -> UnbalRB a c2 h -> UnbalRB a Black (S h)
  RLeft : UnbalRB a Black h -> a -> RB a Black h -> UnbalRB a Red h
  RRight : RB a Black h -> a -> UnbalRB a Black h -> UnbalRB a Red h


total
balance : UnbalRB a Black h -> (c:Colour ** RB a c h)

balance (BalRB t) = (Black ** t)

balance (BLeft (RRLeft (RNode a x b) y c) z d) =
  (Red ** RNode (BNode a x b) y (BNode c z d))

balance (BLeft (RRRight a x (RNode b y c)) z d) =
  (Red ** RNode (BNode a x b) y (BNode c z d))

balance (BLeft (BalRB t) x b) =
  (Black ** BNode t x b)

balance (BLeft t@(BLeft _ _ _) y c) =
  (Black ** BNode (snd (balance t)) y c)

balance (BLeft t@(BRight _ _ _) y c) =
  (Black ** BNode (snd (balance t)) y c)

-- New!
balance (BLeft (RLeft t x b) y c) =
  case balance t of
    (Red ** t2) => balance (BLeft (RRLeft t2 x b) y c)
    (Black ** t2) =>  (Black ** BNode (RNode t2 x b) y c)

-- Also needs
--   BLeft  (RRight b x t) y c
--   BRight c y (RLeft t x b) // ?
--   BRight b x (RRight c y t)

balance (BRight a x (RRLeft (RNode b y c) z d)) =
  (Red ** RNode (BNode a x b) y (BNode c z d))

balance (BRight a x (RRRight b y (RNode c z d))) =
  (Red ** RNode (BNode a x b) y (BNode c z d))

balance (BRight a x (BalRB t)) =
  (Black ** BNode a x t)

balance (BRight a x t@(BLeft _ _ _)) =
  (Black ** BNode a x (snd (balance t)))

balance (BRight a x t@(BRight _ _ _)) =
  (Black ** BNode a x (snd (balance t)))

-- Now, is it possible to write...
-- insert : Ord a => a -> RB a c h -> (c:Colour ** UnbalRB a c h)

-- insert a (RBNil) = (Red ** BalRB (leaf Red a))

-- insert a t@(BNode l x r) =
--   case compare a x of
--     EQ => (Black ** BalRB t)
--     LT => (Black ** BLeft (snd (insert a l)) x r)
--     GT => (Black ** BRight l x (snd (insert a r)))

-- insert a t@(RNode l x r) =
--   case compare a x of
--     EQ => (Red ** BalRB t)
--     LT =>
--       case insert a l of
--         (Black ** l2) => (Red ** ) TODO
