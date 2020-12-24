% guess matching
match(M,W) :- manAssignsScore(M,_,_), womanAssignsScore(W,_,_), not nonMatch(M,W).
nonMatch(M,W) :- manAssignsScore(M,_,_), womanAssignsScore(W,_,_), not match(M,W).

:- manAssignsScore(M,_,_), not jailed(M).

% no singles
jailed(M) :- match(M,_).

% no polygamy
:- match(M1,W), match(M,W), M != M1.
:- match(M,W), match(M,W1), W != W1.
