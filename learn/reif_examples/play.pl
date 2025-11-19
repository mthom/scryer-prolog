% greater_than_two(Y,true) :-  Y #> 2.
% greater_than_two(Y,false) :-  Y #=< 2.

greater_than_two(Y, true) :- Y #> 2.

pound_gt_t(X,Y,T) :- if_(Y #< X, T=true, T=false).
 
weird:-  if_(X #< 3,  Y=X , Y=7), tmember(X, [1,9,3,-1, 0]). 


 