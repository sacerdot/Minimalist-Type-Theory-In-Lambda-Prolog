module basic.

nat z.
nat (s X) :- nat X.


append nil L L.
append (X::L) M (X::N) :- append L M N.

mappend mnil L L.
mappend (mcons X L) M (mcons X N) :- mappend L M N.

nodes emp nil.
nodes (node X T1 T2) (X::L) :-
      nodes T1 L1,
      nodes T2 L2,
      append L1 L2 L.
