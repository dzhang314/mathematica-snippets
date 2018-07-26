(* ::Package:: *)

(* Generate the permutation matrix corresponding
	to a given permutation perm. *)
permutationMatrix = Compile[{{perm, _Integer, 1}},
	Module[{mat = Table[0, {Length@perm}, {Length@perm}]},
		Do[mat[[i, perm[[i]]]] = 1,
			{i, Length@perm}];
		mat]];

(* Find the set of permutations under which the list xs is invariant. *)
stabilizerSubgroup[xs_List] := Select[
	Permutations @ Range @ Length @ xs,
	xs[[#]] === xs &];

(* Count the number of elements of the list xs that
	change when the permutation perm is applied. *)
countChanges[xs_List, perm_List] := Length @ Select[
	Transpose @ {xs, xs[[perm]]}, Not @* Apply[SameQ]];
