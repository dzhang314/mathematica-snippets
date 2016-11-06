(* ::Package:: *)

toStringJoin = Apply[StringJoin] @* Map[ToString];
stringJoinTo[str1_String][str2_String] := StringJoin[str1, str2];
lineJoin[lines_List, end_String, indent_String, endMark_?BooleanQ] :=
	indent <> riffleJoin[lines, end <> "\n" <> indent] <> If[endMark, end, ""];

dualOrder = 4;

duSuffixes = toStringJoin /@ Rest@Subsets@Range[0, dualOrder - 1];
memNames = Prepend[stringJoinTo["du"] /@ duSuffixes, "re"];
longMemNames = Prepend[stringJoinTo["dual"] /@ duSuffixes, "real"];
rhsNames = stringJoinTo["rhs."] /@ memNames;

numLen = StringLength@ToString[2^dualOrder];
tempDecls = Table[
	"const T temp" <> intString[i, numLen] <> " = ",
	{i, 0, 2^dualOrder - 1}];
tempAssns = Table[
	memNames[[i + 1]] <> " = temp" <> intString[i, numLen],
	{i, 0, 2^dualOrder - 1}];

sp4 = "    ";
sp8 = "        ";
sp12 = "            ";

argListCode = lineJoin[
	stringJoinTo["const T &"] /@ longMemNames,
	",", sp8, False];
memInitCode = lineJoin[
	#1 <> "(" <> #2 <> ")" & @@@ Transpose@{memNames, longMemNames},
	",", sp8, False];
tempAssnCode = lineJoin[
	tempAssns,
	";", sp8, True];
memDeclCode = lineJoin[
	stringJoinTo["T "] /@ memNames,
	";", sp4, True];
addEqCode = lineJoin[
	#1 <> " += " <> #2 & @@@ Transpose@{memNames, rhsNames},
	";", sp8, True];
subEqCode = lineJoin[
	#1 <> " -= " <> #2 & @@@ Transpose@{memNames, rhsNames},
	";", sp8, True];

Import@FileNameJoin[{NotebookDirectory[], "dualNumber-v2.wl"}];

prodExprs = Table[memNames[[#1]] <> "*" <> rhsNames[[#2]] & @@@
		dualMultiplicationData[dualOrder][i] // riffleJoin[" + "],
	{i, 2^dualOrder}];
mulCode = lineJoin[
	StringJoin /@ Transpose@{tempDecls, prodExprs},
	";", sp8, True];
