
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
                          (right: RBTree p y elem) -> RBTree (if x == Black && y == Black then (S p) else p) col elem
      NodeLh : Ord elem => (left: RBTree (S p) _ elem) -> (val: elem) -> (col: Colour) ->
                          (right: RBTree p _ elem) -> RBTree (S p) col elem
      NodeRh : Ord elem => (left: RBTree p _ elem) -> (val: elem) -> (col: Colour) ->
                          (right: RBTree (S p) _ elem) -> RBTree (S p) col elem
      NodeAll : Ord elem => (left: RBTree _ _ elem) -> (val: elem) -> (col: Colour) ->
                          (right: RBTree _ _ elem) -> RBTree _ col elem


makeBlack : RBTree p _ elem -> RBTree p Black elem
makeBlack (NodeEq left val _ right) = NodeEq left val Black right
makeBlack (NodeLh left val _ right) = NodeLh left val Black right
makeBlack (NodeRh left val _ right) = NodeRh left val Black right

-- NodeEqBl : Ord elem => (left: RBTree p Black elem) -> (val: elem) -> (col: Colour) -> (h: Nat) -> (right: RBTree p Black elem) -> RBTree (S p) col elem
-- NodeEqRe : Ord elem => (left: RBTree p Red elem) -> (val: elem) -> (col: Colour) -> (h: Nat) -> (right: RBTree p Red elem) -> RBTree p col elem

balanceLh : Ord elem => RBTree (S p) col elem -> elem -> Colour -> RBTree p col elem -> RBTree (S (S p)) col elem
balanceLh (NodeLh (NodeAll a x Red b) y Red c) z Black d = NodeEq (NodeAll a x Black b) y Red (NodeAll c z Black d)
balanceLh (NodeLh a x Red (NodeAll b y Red c)) z Black d = NodeEq (NodeAll a x Black b) y Red (NodeAll c z Black d)

balanceRh : Ord elem => RBTree q col elem -> elem -> Colour -> RBTree p col elem -> RBTree (S p) col elem
balanceRh a x Black (NodeRh (NodeAll b y Red c) z Red d) = NodeEq (NodeAll a x Black b) y Red (NodeAll c z Black d)
balanceRh a x Black (NodeRh b y Red (NodeAll c z Red d)) = NodeEq (NodeAll a x Black b) y Red (NodeAll c z Black d)
