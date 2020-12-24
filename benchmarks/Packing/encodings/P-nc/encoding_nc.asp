int(X) :- area(X,Fv1).
int(X) :- area(Fv1,X).
int(X) :- int(Y), X=Y-1, X>=0.

{pos(I,X,Y)} :- square(I,D), area(W,H), int(X), int(Y), X >= 0, Y >= 0, X1 = X + D, Y1 = Y + D, W >= X1, H >= Y1.




pos_square(I) :- pos(I,X,Y).
:- square(I,D), not pos_square(I).
