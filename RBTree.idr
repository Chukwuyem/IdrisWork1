
module RBTree

public export
data Colour = Red | Black

public export
data RBTree : Type -> Type where
      Empty : Ord elem => RBTree elem
      Node : Ord elem => (left: RBTree elem) -> (val: elem) -> (col: Colour) -> (right: RBTree elem) ->
                        RBTree elem

public export
makeBlack : RBTree elem -> RBTree elem
makeBlack (Node left val _ right) = Node left val Black right

---balance left x col right => Node left val col right
balance : Ord elem => RBTree elem -> elem -> Colour -> RBTree elem -> RBTree elem
balance (Node (Node a x Red b) y Red c) z Black d = Node (Node a x Black b) y Red (Node c z Black d)
balance (Node a x Red (Node b y Red c)) z Black d = Node (Node a x Black b) y Red (Node c z Black d)
balance a x Black (Node (Node b y Red c) z Red d) = Node (Node a x Black b) y Red (Node c z Black d)
balance a x Black (Node b y Red (Node c z Red d)) = Node (Node a x Black b) y Red (Node c z Black d)
balance left val col right = (Node left val col right)

public export
-- from okasaki - red-black trees in a functional setting
insert : elem -> RBTree elem -> RBTree elem
insert x s = makeBlack (ins s)
  where ins Empty = Node Empty x Red Empty
        ins orig@ (Node left val col right) = case compare x val of
                                              LT => balance (ins left) val col right
                                              EQ => orig
                                              GT => balance left val col (ins right)
