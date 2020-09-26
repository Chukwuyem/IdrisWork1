
module RBTree3

data Colour = Red | Black

eq_color : Colour -> Colour -> Bool
eq_color Red Red = True
eq_color Black Black = True
eq_color _ _ = False

Eq (Colour) where
  (==) = eq_color

data RBTree : Nat -> Colour -> Type -> Type where
      Empty : Ord elem => RBTree Z Black elem
      NodeEq : Ord elem => (left: RBTree p x elem) -> (val: elem) -> (col: Colour) ->
                          (h: Nat) -> (right: RBTree p y elem) -> RBTree (if x == Black && y == Black then (S p) else p) col elem
      NodeLh : Ord elem => (left: RBTree (S p) _ elem) -> (val: elem) -> (col: Colour) ->
                            (h: Nat) -> (right: RBTree p _ elem) -> RBTree (S p) col elem
      NodeRh : Ord elem => (left: RBTree p _ elem) -> (val: elem) -> (col: Colour) ->
                            (h: Nat) -> (right: RBTree (S p) _ elem) -> RBTree (S p) col elem


makeBlack : RBTree p _ elem -> RBTree p Black elem
makeBlack (NodeEq left val _ bh right) = NodeEq left val Black bh right
makeBlack (NodeLh left val _ bh right) = NodeLh left val Black bh right
makeBlack (NodeRh left val _ bh right) = NodeRh left val Black bh right


-- NodeEqBl : Ord elem => (left: RBTree p Black elem) -> (val: elem) -> (col: Colour) -> (h: Nat) -> (right: RBTree p Black elem) -> RBTree (S p) col elem
-- NodeEqRe : Ord elem => (left: RBTree p Red elem) -> (val: elem) -> (col: Colour) -> (h: Nat) -> (right: RBTree p Red elem) -> RBTree p col elem


balanceLh : Ord elem => RBTree p col elem -> elem -> Colour -> Nat -> RBTree q col elem -> RBTree (S p) col elem
balanceLh (NodeLh (NodeEq a x Red n b) y Red n c) z Black n d = NodeEq (NodeEq a x Black n b) y Red (S n) (NodeEq c z Black n d)
