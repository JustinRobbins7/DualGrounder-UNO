int(X) :- area(X,Fv1).
int(X) :- area(Fv1,X).
int(X) :- int(Y), X=Y-1, X>=0.

{pos(I,X,Y)} :- square(I,D), area(W,H), int(X), int(Y), X >= 0, Y >= 0, X1 = X + D, Y1 = Y + D, W >= X1, H >= Y1.

:- pos(I,X,Y), pos(I,X1,Y1), X1 != X.
:- pos(I,X,Y), pos(I,X1,Y1), Y1 != Y.

pos_square(I) :- pos(I,X,Y).
:- square(I,D), not pos_square(I).

%top left
:- pos(I1,X1,Y1), square(I1,D1), pos(I2,X2,Y2), square(I2,D2), I1 != I2, W1 = X1+D1, H1 = Y1+D1, X2 >= X1, X2 < W1, Y2 >= Y1, Y2 < H1.
%bottom left 
:- pos(I1,X1,Y1), square(I1,D1), pos(I2,X2,Y2), square(I2,D2), I1 != I2, W1 = X1+D1, H1 = Y1+D1, H2 = Y2+D2, X2 >= X1, X2 < W1, H2 > Y1, H2 <= H1.

