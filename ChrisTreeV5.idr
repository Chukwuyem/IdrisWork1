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


--total
balance : UnbalRB a Black h -> (c:Colour ** RB a c h)

balance (BalRB t) = (Black ** t)

balance (BLeft (RRLeft (RNode a x b) y c) z d) = (Red ** RNode (BNode a x b) y (BNode c z d))

balance (BLeft (RRRight a x (RNode b y c)) z d) = (Red ** RNode (BNode a x b) y (BNode c z d))

balance (BLeft (BalRB t) x b) = (Black ** BNode t x b)

balance (BLeft t@(BLeft _ _ _) y c) = (Black ** BNode (snd (balance t)) y c)

balance (BLeft t@(BRight _ _ _) y c) = (Black ** BNode (snd (balance t)) y c)

balance (BLeft (RLeft t x b) y c) =
  case balance t of
    (Red ** t2) => balance (BLeft (RRLeft t2 x b) y c)
    (Black ** t2) =>  (Black ** BNode (RNode t2 x b) y c)

balance (BLeft (RRight b x t) y c) =
  case balance t of
    (Red ** t2) => balance (BLeft (RRRight b x t2) y c)
    (Black ** t2) => (Black ** BNode (RNode b x t2) y c)

balance (BRight c y (RLeft t x b)) =
  case balance t of
    (Red ** t2) => balance (BRight c y (RRLeft t2 x b))
    (Black ** t2) => (Black ** BNode c y (RNode t2 x b))

balance (BRight c y (RRight b x t)) =
  case balance t of
    (Red ** t2) => balance (BRight c y (RRRight b x t2))
    (Black ** t2) => (Black ** BNode c y (RNode b x t2))

balance (BRight a x (RRLeft (RNode b y c) z d)) = (Red ** RNode (BNode a x b) y (BNode c z d))

balance (BRight a x (RRRight b y (RNode c z d))) = (Red ** RNode (BNode a x b) y (BNode c z d))

balance (BRight a x (BalRB t)) = (Black ** BNode a x t)

balance (BRight a x t@(BLeft _ _ _)) = (Black ** BNode a x (snd (balance t)))

balance (BRight a x t@(BRight _ _ _)) = (Black ** BNode a x (snd (balance t)))


insert : Ord a => a -> RB a c h -> UnbalRB a c h
-- insert a (RBNil) = (Red ** BalRB (leaf Red a))

insert a t@(BNode l x r) =
  case compare a x of
    EQ => BalRB t
    LT =>
      case l of
        RBNil => BLeft (BalRB(leaf Red a)) x r
        BNode _ _ _ => BLeft (insert a l) x r
        RNode _ _ _ => BLeft (insert a l) x r
    GT =>
      case l of
        RBNil => BRight l x (BalRB(leaf Red a))
        BNode _ _ _ => BRight l x (insert a r)
        RNode _ _ _ => BRight l x (insert a r)

insert a t@(RNode l x r) =
  case compare a x of
    EQ =>  BalRB t
    LT =>
      case l of
        RBNil => RRLeft (leaf Red a) x r
        BNode _ _ _ => RLeft (insert a l) x r
    GT =>
      case l of
        RBNil => RRRight l x (leaf Red a)
        BNode _ _ _ => RRight l x (insert a r)
