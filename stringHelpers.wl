(* ::Package:: *)

riffleJoin[xs_List /; AllTrue[StringQ, xs], sep_String] :=
	StringJoin @@ Riffle[xs, sep];
(* operator form *)
riffleJoin[sep_String][xs_List /; AllTrue[StringQ, xs]] :=
	StringJoin @@ Riffle[xs, sep];

intString[n_Integer, p_Integer] :=
	StringJoin @@ ToString /@ PadLeft[IntegerDigits[n], p];
(* operator form *)
intString[p_Integer][n_Integer] :=
	StringJoin @@ ToString /@ PadLeft[IntegerDigits[n], p];
