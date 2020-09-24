#!/usr/bin/env python3

# Node representation is a record {v, b, h, l, r} and we use None to represent
# empty. Black height (bh) is the number of black nodes on any simple path from
# a node x (not including it) to a leaf. We'll use False for red and True for
# black.


class Empty:
    def __init__(self):
        pass

    def __repr__(self):
        return "∅"

    def is_black(self):
        return True

    def black_height(self):
        return 0

    def inclusive_black_height(self):
        return 1 if self.is_black() else 0

    def is_empty(self):
        return True


EMPTY = Empty()


class Node:
    def __init__(self, value, black=True, left=EMPTY, right=EMPTY):
        self.value = value
        if not black:
            assert left.is_black()
            assert right.is_black()
        self.black = black
        self.left = left
        self.right = right
        self.height = left.inclusive_black_height()
        assert self.height == right.inclusive_black_height()

    def __repr__(self):
        buf = "(%s%c%d" % (self.value, "*" if self.black else "!", self.black_height())
        if self.left.is_empty() and self.right.is_empty():
            buf += ")"
        else:
            buf += " %s %s)" % (self.left, self.right)
        return buf

    def is_black(self):
        return self.black

    def is_empty(self):
        return False

    def black_height(self):
        return self.height

    def inclusive_black_height(self):
        if self.is_black():
            return self.height + 1
        else:
            return self.height
