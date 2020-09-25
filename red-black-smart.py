#!/usr/bin/env python3

# Node representation is a record (v, b, l, r) and we use None to represent
# empty. Black height (bh) is the number of black nodes on any simple path from
# a node x (not including it) to a leaf. We'll use False for red and True for
# black.


def is_empty(node):
    return node is None


def is_black(node):
    if is_empty(node):
        return True
    else:
        (_, black, _, _) = node
        return black


def get_left(node):
    assert not is_empty(node)
    (_, _, left, _) = node
    return left


def get_right(node):
    assert not is_empty(node)
    (_, _, _, right) = node
    return right


def get_value(node):
    assert not is_empty(node)
    (value, _, _, _) = node
    return value


# Max number of black nodes on any path from node (not including it) to a leaf.
def black_height(node):
    if is_empty(node):
        return 0
    else:
        hl = inclusive_black_height(get_left(node))
        hr = inclusive_black_height(get_right(node))
        return max(hl, hr)


def inclusive_black_height(node):
    if is_empty(node):
        return 1
    else:
        h = black_height(node)
        if is_black(node):
            h += 1
        return h


# Smart constructor that flags any violations of tree invariants.
def make_node(value, black=True, left=None, right=None):
    node = (value, black, left, right)
    if not black:
        assert is_black(left), "Red-Red on left: %s" % (node,)
        assert is_black(right), "Red-Red on right: %s" % (node,)
    hl = inclusive_black_height(left)
    hr = inclusive_black_height(right)
    assert hl == hr, "Mismatched heights:\n  left=%d: %s\n right=%d: %s" % (
        hl,
        left,
        hr,
        right,
    )
    return node


def update_color(node, black=True):
    return make_node(get_value(node), black, get_left(node), get_right(node))


def insert_recursive(root, value):
    if is_empty(root):
        return make_node(value, black=False)
    else:
        if value < get_value(root):
            new_left = insert_recursive(get_left(root), value)
            return make_node(get_value(root), is_black(root), new_left, get_right(root))
        else:
            new_right = insert_recursive(get_right(root), value)
            return make_node(get_value(root), is_black(root), get_left(root), new_right)


def insert(root, value):
    return update_color(insert_recursive(root, value))
