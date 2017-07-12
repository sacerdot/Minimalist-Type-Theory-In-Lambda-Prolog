sig basic. 

% Type and constructors for natural numbers
kind nt type.
type z nt.
type s nt -> nt.

type nat nt -> o.
type append (list A) -> (list A) -> (list A) -> o.

% Lists with mixed-type elements. 
kind mlist type.
type mnil mlist.
type mcons A -> mlist -> mlist.

type mappend mlist -> mlist -> mlist -> o.

% Binary trees

kind btree type -> type.

type emp (btree A).
type node A -> (btree A) -> (btree A) -> (btree A).

type nodes (btree A) -> (list A) -> o.
