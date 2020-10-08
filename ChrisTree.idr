-- Black node can have red or black child nodes.
-- Red node can only have black child nodes.

data Colour = Red | Black

incrementIfBlack : Colour -> Nat -> Nat
incrementIfBlack Black n = S n
incrementIfBlack Red n = n

data Triad : (parent:Colour) ->  (left:Colour) -> (right:Colour) -> Type where
  R : Triad Red Black Black
  B : Triad Black c1 c2

data RBTree : Type -> Colour -> Nat -> Type where
  RBNil : RBTree elem Black 0
  RBNode : Triad c c1 c2
       -> elem
       -> RBTree elem c1 h
       -> RBTree elem c2 h
       -> RBTree elem c (incrementIfBlack c h)

leaf : Triad c Black Black -> elem -> RBTree elem c (incrementIfBlack c 0)
leaf c elem = RBNode c elem RBNil RBNil

-- The following definitions assemble the tree pictured at
-- https://upload.wikimedia.org/wikipedia/commons/thumb/6/66/Red-black_tree_example.svg/1920px-Red-black_tree_example.svg.png

example : RBTree Int Black 2
example =
  RBNode B 13
  (RBNode R 8 (RBNode B 1 RBNil (leaf R 6)) (leaf B 11))
  (RBNode R 17 (leaf B 15) (RBNode B 25 (leaf R 22) (leaf R 27)))

-- But we can't have two consecutive reds (this should throw type mismatch):
-- λ> RBNode R 'A' (leaf R 'B') RBNil

-- And we can't imbalance black:
-- λ> RBNode B 'A' (RBNode B 'B' (leaf B 'C') RBNil) RBNil

-- It's always possible to make the root of a tree black, but it might increase
-- the height.

incrementIfRed : Colour -> Nat -> Nat
incrementIfRed Red n = S n
incrementIfRed Black n = n

total
makeBlack : RBTree e c h -> RBTree e Black (incrementIfRed c h)
makeBlack (RBNode B e l r) = RBNode B e l r
makeBlack (RBNode R e l r) = RBNode B e l r
makeBlack RBNil = RBNil

total
contains : Ord e => RBTree e c h -> e -> Bool
contains RBNil _ = False
contains (RBNode _ e l r) goal with (compare goal e)
  | EQ = True
  | LT = contains l goal
  | GT = contains r goal


data Unbal : Type -> Colour -> Nat -> Type where
  UnNil : Unbal elem Black 0
  UnNode : (c : Colour)
    -> elem
    -> RBTree elem c1 h
    -> RBTree elem c2 h
    -> Unbal elem c (incrementIfBlack c h)

  
--total  -- Not sure what cases are missing?
rebalanceLeft
  : elem
  -> Unbal elem c1 h
  -> RBTree elem c2 h
  -> (c : Colour ** RBTree elem c (S h))

rebalanceLeft z UnNil d = (Black ** RBNode B z RBNil d)

rebalanceLeft z (UnNode Black y a b) c =
  (Black ** RBNode B z (RBNode B y a b) c)

rebalanceLeft z (UnNode Red y (RBNode R x a b) c) d =
  (Red ** RBNode R y (RBNode B x a b) (RBNode B z c d))

rebalanceLeft z (UnNode Red x a (RBNode R y b c)) d =
  (Red ** RBNode R y (RBNode B x a b) (RBNode B z c d))

rebalanceLeft z (UnNode Red y t@(RBNode B _ _ _) v@(RBNode B _ _ _)) c =
  (Black ** RBNode B z (RBNode R y t v) c)

-- Trying out base case that actually has 2 nodes above nil. If both nodes are
-- black, that would be height 2? But if it's black-red that would be height 1.

-- All trees of height 1:
--   (B nil nil)
--   (B (R nil nil) nil)
--   (B nil (R nil nil))
--   (B (R nil nil) (R nil nil))

total
insertAtLeftRedLeaf : Ord elem => elem -> RBTree elem Red 0 -> elem -> Maybe (RBTree elem Red 1)
insertAtLeftRedLeaf y (RBNode R x _ _) new =
  -- We're assuming x<y because this is a left-leaf of y.
  case compare new x of
    EQ => Nothing
    LT =>
      -- Order is: new < x < y
      Just (RBNode R x (leaf B new) (leaf B y))
    GT =>
      -- Order is: x < new < y
      Just (RBNode R new (leaf B x) (leaf B y))

--total -- Can't get totality here either :(

insert1 : Ord elem => RBTree elem Black 1 -> elem -> (c : Colour ** RBTree elem c 1)
insert1 t@(RBNode B x l r) new =
  case compare new x of
    EQ => (Black ** t)
    LT =>
      case l of
        RBNil => (Black ** RBNode B x (leaf R new) r)
        RBNode R w RBNil RBNil =>
          case compare new w of
            EQ => (Black ** t)
            LT => (Red ** RBNode R w (leaf B new) (leaf B x))
            GT => (Red ** RBNode R new (leaf B w) (leaf B x))
    GT =>
      case r of
        RBNil => (Black ** RBNode B x l (leaf R new))
        RBNode R y RBNil RBNil =>
          case compare new y of
            EQ => (Black ** t)
            LT => (Red ** RBNode R new (leaf B x) (leaf B y))
            GT => (Red ** RBNode R y (leaf B x) (leaf B new))


--t2 : RBTree Char Black 1
-- t2 = snd (insert1 (leaf B 'X') 'W')

-- insert1 (RBNode B y (RBNode R x RBNil RBNil) RBNil) = True
-- insert1 (RBNode B y RBNil (RBNode R z RBNil RBNil)) = True
-- insert1 (RBNode B y (RBNode R x RBNil RBNil) (RBNode R z RBNil RBNil)) = True
