(* ::Package:: *)

circuitQ[expr_] := Or[
	Head[expr] === resistor,
	Head[expr] === seriesCircuit,
	Head[expr] === parallelCircuit
];

circuitGraphics[circuit_?circuitQ] := Graphics[{
	Line[{{0, 0}, {1, 0}}],
	circuit // at[1, 0],
	Line[{{width[circuit]+1, 0}, {width[circuit]+2, 0}}]
}];


width[resistor[_]] = 1;
height[resistor[_]] = 1;

resistor[r_] // at[x_, y_] := {
	Line[Table[{x + dx, y + Sin[6\[Pi]*dx]/6}, {dx, 0, 1, 1/12}]],
	Text[Style[StringForm["``\[CapitalOmega]", r], Bold, FontSize -> 12], {x + 0.5, y + 0.4}]
};


SetAttributes[seriesCircuit, {Flat, OneIdentity, Orderless}];

width[seriesCircuit[components__]] :=
	Total[width /@ {components}] + Length[{components}] - 1;
height[seriesCircuit[components__]] := Max[height /@ {components}];

seriesCircuit[components__] // at[x_, y_] := Module[
	{comps, n, widthSums},
	comps = {components};
	n = Length[comps];
	widthSums = Prepend[Accumulate[width /@ comps], 0];
	Append[
		Table[Line[{
				{x + (i-1) + widthSums[[i+1]], y},
				{x + i + widthSums[[i+1]], y}
			}], {i, n-1}],
		Join @@ Table[comps[[i]] // at[x + (i-1) + widthSums[[i]], y],
			{i, n}]
	]
];


SetAttributes[parallelCircuit, {Flat, OneIdentity, Orderless}];

width[parallelCircuit[components__]] := Max[width /@ {components}] + 2;
height[parallelCircuit[components__]] := Total[height /@ {components}];

parallelCircuit[components__] // at[x_, y_] := Module[
	{comps, n, h, w, xright, xmid, ytop, ybot, ypos},
	comps = {components};
	n = Length[comps];
	h = height /@ comps;
	w = width /@ comps;
	xright = x + 2 + Max[w];
	xmid = Mean[{x, xright}];
	ytop = y + Total[h]/2;
	ybot = y - Total[h]/2;
	ypos = ytop - Most@Prepend[Accumulate[h], 0] - h/2;
	Join[
		Join @@ Table[comps[[i]] // at[xmid - w[[i]]/2, ypos[[i]]], {i, n}],
		Table[Line[{{x, ypos[[i]]}, {xmid - w[[i]]/2, ypos[[i]]}}], {i, n}],
		Table[Line[{{xright, ypos[[i]]}, {xmid + w[[i]]/2, ypos[[i]]}}], {i, n}],
		Line[{{#, ytop - First[h]/2}, {#, ybot + Last[h]/2}}] & /@ {x, xright}
	]
];
