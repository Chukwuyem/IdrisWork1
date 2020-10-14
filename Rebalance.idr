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
  RLeft : RB a Red h -> a -> RB a Black h -> UnbalRB a Red h
  RRight : RB a Black h -> a -> RB a Red h -> UnbalRB a Red h
  BLeft : UnbalRB a c1 h -> a -> RB a c2 h -> UnbalRB a Black (S h)
  BRight : RB a c1 h -> a -> UnbalRB a c2 h -> UnbalRB a Black (S h)


total
balance : UnbalRB a Black h -> (c:Colour ** RB a c h)

balance (BalRB t) = (Black ** t)

balance (BLeft (RLeft (RNode a x b) y c) z d) =
  (Red ** RNode (BNode a x b) y (BNode c z d))

balance (BLeft (RRight a x (RNode b y c)) z d) =
  (Red ** RNode (BNode a x b) y (BNode c z d))

balance (BLeft (BalRB t) x b) =
  (Black ** BNode t x b)

balance (BLeft t@(BLeft _ _ _) y c) =
  (Black ** BNode (snd (balance t)) y c)

balance (BLeft t@(BRight _ _ _) y c) =
  (Black ** BNode (snd (balance t)) y c)

balance (BRight a x (RLeft (RNode b y c) z d)) =
  (Red ** RNode (BNode a x b) y (BNode c z d))

balance (BRight a x (RRight b y (RNode c z d))) =
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
