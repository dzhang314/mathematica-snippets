(* ::Package:: *)

cppForm`DeclareVars[type_String, {}] := {};
cppForm`DeclareVars[type_String, varNames_List] := Block[{
		lines = {}, tempLine, i = 1,
		curLine = type <> " " <> varNames[[1]]
	},
	While[++i <= Length[varNames],
		tempLine = curLine <> ", " <> varNames[[i]];
		If[StringLength@tempLine > 70,
			AppendTo[lines, curLine <> ", "];
			curLine = "    " <> varNames[[i]],
		(* else *)
			curLine = tempLine
		]
	];
	Append[lines, curLine]
];


(* ::Section:: *)
(*Legacy*)


(* cppForm -- Converting Mathematica numeric constants to C++ literals. *)

cppForm[n_Integer] := ToString[n];

(* TODO: Real and Complex constants *)


cppForm`DeclareRegisters[{type_Symbol, n_Integer}] :=
	cppForm`DeclareVars[cppForm[type],
		cppForm`abbrev[type] <> ToString[#] & /@ Range[0, n-1]];

cppForm::tensorExperimental = "Currently, support for tensors is experimental \
in cppForm. Output code will likely require human editing before use.";

cppForm`DeclareRegisters[{MTensor, n_Integer}] := (
	Message[cppForm::tensorExperimental];
	{});

cppForm`DeclareRegisters[x_] := Throw@StringForm[
	"Unrecognized register type ``", x];


cppForm`DeclareArgument[type_Symbol, n_Integer] := cppForm`DeclareVars[
	{cppForm[type], "intent(in)"}, {"arg" <> ToString[n]}];

cppForm`DeclareArgument[MTensor[type_Symbol, r_Integer], n_Integer] := Module[
	{colons = "(" <> riffleJoin[ConstantArray[":", r], ","] <> ")"},
	cppForm`DeclareVars[{cppForm[type], "intent(in)"},
		{"arg" <> ToString[n] <> colons}]];


(* ::Subsection:: *)
(*Translating Instructions*)


cppForm@Instruction["Jump", Line[n_Integer]] := "go to " <> ToString[n];

cppForm@Instruction[Return] = "return";

cppForm@Instruction["LoopIncr",
	{index_Register, limit_Register}, label_Integer]:=
		ToString@StringForm["`1` = `1` + 1; if (`1` <= `2`) go to `3`",
			cppForm[index], cppForm[limit], cppForm[label]];


cppForm@Instruction["SetComplex", dst_Register, {re_, im_}] :=
	ToString@StringForm["`1` = dcmplx(`2`, `3`)",
		cppForm[dst], cppForm[re], cppForm[im]];


cppForm@Instruction["FunctionCall", "MinI", dst_Register, args_List] := (
	Assert[AllTrue[args, Head[#] === Register &]];
	ToString@StringForm["`1` = min(`2`)", cppForm[dst],
		riffleJoin[cppForm /@ args, ", "]]);


cppForm@Instruction[List, {n_Integer}, dst_Register, src_List] := (
	Assert[n === Length[src]];
	Assert[Head@First[dst] === MTensor];
	cppForm[dst] <> " = [" <> riffleJoin[cppForm /@ src, ", "] <> "]");

cppForm@Instruction[Table, dst_Register, dims_List] :=
	ToString@StringForm["allocate(`1`(`2`))",
		cppForm[dst], riffleJoin[cppForm /@ dims, ", "]];

cppForm@Instruction[Length, dst_Register, src_] := (
	Assert[First[dst] === Integer];
	Assert[Head@First[src] === MTensor];
	ToString@StringForm["`1` = size(`2`)", cppForm[dst], cppForm[src]]);
