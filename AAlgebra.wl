(* ::Package:: *)

BeginPackage["AAlgebra`",{"Macros`"}];
`Private`allfunctions=Hold[
 NonCommutativeMultiply,
 AExpand,
 ACollect,
 AMonomialRules,
 AValidate,
 AClass,
 AOfClassQ,
 AOrder,
 AClassOrder,
 AOrderWithinClass,
 ADeclareProduct,
 ADeclareCommutator,
 ADeclareAnticommutator,
 PartialD,
 $AMaxPower
];

Begin["`Private`"];

Unprotect@@allfunctions;
ClearAll@@allfunctions;

(*TODO: in AMonomialRules, sort the association by exponent*)
(*TODO: maybe only look for commutativity (hence ugly brackets)
in terms with only two factors and in factors of same class?*)
(*TODO: in AExpand, build a more clever order.*)
(*TODO: in ACollect and AMonomialRules, build a more clever order for AExpand,
as the current one breaks with e.g. patt={x,_,x}.*)
(*TODO: document and implement ACollect[expr,{x1,{{x2,{_,y2}},y1}}] for
nested collection with more control on the left/right order.*)
(*TODO: write proper documentation pages, shorten usage strings.*)
(*TODO: the final AExpand in ACollect is a bit too eager and may send
a(b**c) to (ab)**c when we try to collect {_,b|c}.*)

(*Usage["The expression $a/b+a/b$ is equal to $2a/b$"] will pretty-print
what's between dollars.*)
HoldPattern[Usage[str_]]:=
StringReplace[str,"$"~~Shortest[a___]~~"$":>
  With[{expr=MakeExpression[a,StandardForm]/.HoldComplete->HoldForm},
       If[Head[expr]===ErrorBox,a,
          "\!\(\*"<>
          ToString[ToBoxes[
            expr/.x_Symbol/;LowerCaseQ[ToString[x]]:>Style[x,"TI"],
            StandardForm]/.
            (StripOnInput->False):>Sequence[]//.
            TagBox[x_,HoldForm]:>x,
           InputForm]<>"\)"]]];

AExpand::usage=Usage@"\
$AExpand[expr, options]$ or equivalently $AExpand[options][expr]$ \
distributes non-commutative products and applies commutation rules and product \
rules (see $ADeclareAnticommutator$, $ADeclareCommutator$, $ADeclareProduct$) in \
an effort to order factors according to the preferred order (see $AOrder$). \
\
The product is assumed to be associative: when evaluating $a**b**c$ there is no \
guarantee on whether a rule for $a**b$ or for $b**c$ will apply first. \
\
The function $Expand$ is applied where relevant.  Just like $Expand$, $AExpand$ \
threads over lists, equations, inequalities and logic functions.

$AExpand[\[Ellipsis], Distribute->patt]$ prevents $AExpand$ from distributing terms free of $patt$: if \
$a$ and $b$ match $patt$ and $x$ and $y$ do not then $(x+y+a+b^2)**(x+y+b)$ becomes \
$(x+y)^2+(x+y)**b+a**(x+y)+a**b+b^2**(x+y)+b^3$.

$AExpand[\[Ellipsis], Only->patt]$ prevents $AExpand$ from applying commutation and product rules for \
factors free of $patt$.  A useful pattern is $_?(AOfClassQ[class])$.

$AExpand[\[Ellipsis], Order->{x,y,\[Ellipsis]}]$ causes $AExpand$ to use as the preferred order the order \
where variables matching $x$ are placed to the left of those matching $y$, \
and so on, ending with variables that match none of the patterns.  Variables \
matching the same pattern are ordered according to the default order $AOrder$. \
The pattern $_$ is treated specially: it only matches if no other pattern \
matches (using $_$ twice is an error).  If a variable matches several \
patterns there is no guarantee on which one matches.

$AExpand[\[Ellipsis], Expand->patt]$ causes $AExpand$ to apply $Expand[#,patt]&$ instead of \
$Expand$ to subexpressions.  To disable $Expand$ completely use the pattern $Except[_]$.";

ACollect::usage=Usage@"\
$ACollect[expr, x]$ expands $expr$ using $AExpand$ then collects together \
terms with the same power of (any variable matching) $x$.  The $x$ are factored \
towards the left of the expression.

$ACollect[expr, {x1, x2, \[Ellipsis], _, \[Ellipsis], y2, y1}]$ expands $expr$ using $AExpand$, \
then collects terms according to the powers of (variables matching) $x1$, and \
in each coefficient collects terms according to the powers of $x2$, and so \
on until reaching the general pattern $_$ in the pattern list.  Then powers \
of $y1$ are collected to the right, and in each coefficient powers of $y2$, \
and so on.

$ACollect[expr, vars, h]$ applies $h$ to each coefficient.

$ACollect[\[Ellipsis], Distribute->patt]$ and $Only->patt$ are passed to $AExpand$ as options.  Just \
like $AExpand$, $ACollect$ threads over lists, equations, inequalities and \
logic functions.";

AMonomialRules::usage=Usage@"\
$AMonomialRules[expr, x]$ expands $expr$ and collects terms according to the \
power of (any variable matching) $x$ to the left of the expression.  The \
result is given as an association whose keys are products of variables $x$ \
and whose values are the corresponding coefficients.

$AMonomialRules[expr, {x1, x2, \[Ellipsis], _, \[Ellipsis], y2, y1}]$ gives nested associations \
whose keys are products of variables matching $x1$, then $x2$ and so on, \
then $y1$, $y2$, and so on.  The syntax is the same as $ACollect$.

$AMonomialRules[expr, vars, h]$ applies $h$ to each coefficient.

$AMonomialRules[\[Ellipsis], Distribute->patt, Only->patt]$ are passed to $AExpand$ as options.  \
$AMonomialRules$ threads over lists in $expr$.";

AValidate::usage=Usage@"\
$AValidate[expr]$ checks that usual (commutative) multiplication is only used \
in $expr$ with factors that commute.";

AClass::usage=Usage@"\
$AClass[var]$ gives the class of $var$.  The class of a variable affects the \
preferred ordering in products.  It is declared in the same way as usual \
functions, namely $AClass[patt_]:=c$ declares that variables matching the pattern \
$patt$ have class $c$.  This declaration also adds $c$ (if it is new) to the list of \
classes, whose order defines the default ordering of classes.

$AClass[var]$:=\"number\" is predefined for numeric quantities. \
A non-commutative product with a variable of this class is automatically \
converted to a commutative product.

$AClass[var]$:=\"scalar\" is predefined for variables that commute with all others \
except those of class \"differential\".

$AClass[var]$:=\"differential\" is predefined for differential operators.  It \
includes $PartialD[x]$ (see $PartialD$).";

AOfClassQ::usage=Usage@"\
$AOfClassQ[patt][var]$ is $True$ if $AClass[var]$ matches the pattern $patt$. \
Thus, the pattern $_?(AOfClassQ[patt])$ matches members of any class \
matched by $patt$.";

AOrder::usage=Usage@"\
$AOrder[x, y]$ indicates the preferred order of the variables $x$ and $y$ in \
non-commutative products, to determine whether applicable commutation rules \
should be used.  It is $1$ if $x**y$ is preferred, $-1$ if $y**x$ is, and $0$ if $x===y$. \
It is important that $AOrder[x, y] == -AOrder[y, x]$.

$AOrder[x, y]$ by default compares the variables' classes $AClass[x]$ and \
$AClass[y]$ using $AClassOrder$.  If this gives $0$ (for instance if $x$ and $y$ have \
the same class) then $x$ and $y$ are compared using $AOrderWithinClass$, typically \
the standard $Order$.";

AClassOrder::usage=Usage@"\
$AClassOrder[c, d]$ gives $1$ if variables of class $c$ should be ordered before \
those of class $d$ in non-commutative products (using available commutation rules), \
$-1$ if they should be ordered after, and $0$ if the order is indifferent.  In this \
last case (including the case $c===d$), $AOrderWithinClass$ is used to determine \
the order.  It is important that $AClassOrder[d, c] == -AClassOrder[c, d]$.

$AClassOrder[c, d]$ by default is the order in which classes are declared using \
$AClass[patt]:=c$, except for the class \"differential\" which is placed to the \
very right.";

AOrderWithinClass::usage=Usage@"\
$AOrderWithinClass[x, y, classx, classy]$ is used to determine the preferred \
order $AOrder[x, y]$ of $x$ and $y$ when comparing their classes is not enough \
(when $AClassOrder$ gives $0$).  By default this is the standard $Order[x, y]$.

$AOrderWithinClass[x, y, classx, classy]$ includes the classes of $x$ and $y$ among its arguments so that one can \
more easily defined a custom order for variables of a specific class.  It is \
important that $AOrderWithinClass[y, x, classy, classx] == \
-AOrderWithinClass[x, y, classx, classy]$.";

ADeclareProduct::usage=Usage@"\
$ADeclareProduct[x**y :> rhs, \[Ellipsis]]$ declares one or more rules for the \
product of two variables (or patterns), namely it declares $x**y$ equal to $rhs$. \
A condition can be included in the $rhs$: $ADeclareProduct[x**y:>expr/;cond]$. \
By default, this rule is only used by $AExpand$ if $x$ and $y$ are not in the \
preferred order.

$ADeclareProduct[\[Ellipsis], Apply->True]$ causes the rules being declared to be applied even if $x**y$ is \
already in the preferred order (including the case where they coincide). \
This may lead to infinite recursion if the right-hand side involves $y**x$.";

ADeclareCommutator::usage=Usage@"\
$ADeclareCommutator[{x,y} :> rhs, \[Ellipsis]]$ declares one or more rules for the \
commutator of two variables (or patterns), namely it declares $x**y$ equal to \
$y**x+rhs$ (and conversely $y**x$ equal to $x**y-rhs$).  This rule is used by \
$AExpand$ to bring products in the preferred order.";

ADeclareAnticommutator::usage=Usage@"\
$ADeclareAnticommutator[{x,y} :> rhs, \[Ellipsis]]$ declares one or more rules for \
the anticommutator of two variables (or patterns), namely it declares $x**y$ \
equal to $-y**x+rhs$ (and conversely $y**x$ equal to $-x**y+rhs$).  It also takes \
care of the case where $x$ and $y$ are equal: $x**x$ is declared to be $rhs$/2.  This \
rule is used by $AExpand$ to bring products in the preferred order.";

PartialD::usage=Usage@"\
$PartialD[x]$ represents the partial derivative operator with respect to the \
(scalar) variable $x$.  In products, it can be commuted through any \
expression using $PartialD[x]**y - y**PartialD[x] == D[y, x]$.";

$AMaxPower::usage="Maximum power that is expanded to a noncommutative product (currently not implemented)";

$AMaxPower=100;

(*Before declaring any global rule which involves NonCommutativeMultiply we
make sure to remove its attributes Flat and OneIdentity by running ClearAll[NonCommutativeMultiply].
Flat leads to inefficient pattern matching and to (avoidable with some pain) infinite recursion.
Additionally, the pattern NonCommutativeMultiply[_,_NonCommutativeMultiply] would match any NonCommutativeMultiply[_].
Also define here some basic properties of NonCommutativeMultiply.*)
HoldPattern[NonCommutativeMultiply[]]:=1;
HoldPattern[NonCommutativeMultiply[a_]]:=a;
HoldPattern[NonCommutativeMultiply[a___,NonCommutativeMultiply[b___],c___]]:=
 NonCommutativeMultiply[a,b,c];
HoldPattern[NonCommutativeMultiply[a___,b_?NumericQ,c___]]:=
 Times[b,NonCommutativeMultiply[a,c]];
HoldPattern[NonCommutativeMultiply[a___,b_Times?(MemberQ[_?NumericQ]),c___]]:=
 Times[Times@@Extract[b,#],NonCommutativeMultiply[a,Delete[b,#],c]]&[
  Position[b,_?NumericQ,{1}]];
NonCommutativeMultiply/:HoldPattern[Factor[x_NonCommutativeMultiply]]:=Factor/@x;
NonCommutativeMultiply/:HoldPattern[Expand[x_NonCommutativeMultiply]]:=Expand/@x;
NonCommutativeMultiply/:HoldPattern[Expand[x_NonCommutativeMultiply,patt_]]:=
 Expand[#,patt]&/@x;



(*AClass[var] user-defined class of var.
pClassPos[class] helps control the preferred order.
pClassQ[str_String] is True if str is a class name.*)
ClearAll[pClassQ,pClassPos];
pClassQ[class_String]:=(Head[pClassPos[class]]=!=pClassPos);
SyntaxInformation[AClass]={"ArgumentsPattern"->{_}};
SetArgumentCount[AClass,1];
plastcp=0;
AClass/:HoldPattern[(Set|SetDelayed|TagSet|TagSetDelayed)
  [___,AClass[___],class_String]/;
  If[Not[pClassQ[class]],pClassPos[class]=(plastcp+=10)]]:=Null;
AClass[_?NumericQ]:="number";
AClass[]:="scalar";AClass[]=.;(*Kludge to declare class "scalar" with right priority.*)
AClass[PartialD[_]]:="differential";
pClassPos["differential"]=100000;

(*AOfClassQ[class_][var_]*)
SyntaxInformation[AOfClassQ]={"ArgumentsPattern"->{_}};
SetArgumentCount[AOfClassQ,1];
AOfClassQ/:HoldPattern[Verbatim[PatternTest][_,AOfClassQ]]:=
 Null/;Message[AOfClassQ::pattx];
HoldPattern[AOfClassQ[class_String]/;
 If[Not[pClassQ[class]],Message[AClass::unknown,class]]]:=Null;
HoldPattern[AOfClassQ[class_]]:=(MatchQ[AClass[#],class]&);

(*AOrder[x, y] in terms of AClassOrder[c, d] and AOrderWithinClass[x, y, c, d]*)
SyntaxInformation[AOrder]={"ArgumentsPattern"->{_,_}};
SetArgumentCount[AOrder,2];
HoldPattern[AOrder[x_, y_]]:=
 With[{cx=AClass[x],cy=AClass[y]},
      Switch[AClassOrder[cx,cy],1,1,-1,-1,
             _,AOrderWithinClass[x,y,cx,cy]]];
SyntaxInformation[AClassOrder]={"ArgumentsPattern"->{_,_}};
SetArgumentCount[AClassOrder,2];
HoldPattern[AClassOrder[c_String?pClassQ,d_String?pClassQ]]:=
 If[pClassQ[c]&&pClassQ[d],Order[pClassPos[c],pClassPos[d]],0];
SyntaxInformation[AOrderWithinClass]={"ArgumentsPattern"->{_,_,_,_}};
SetArgumentCount[AOrderWithinClass,4];
HoldPattern[AOrderWithinClass[x_,y_,_,_]]:=Order[x,y];

(*TODO:remove many rules of pProdExpr, now useless.*)
(*Second argument of pProd is of the form x**y.
First argument of pProd gives pOrder[x, y], fewer rules apply when that is -1.*)
ClearAll[pProd,pProdExpr];
SetAttributes[pProd,HoldRest];
HoldPattern[pProd[_,a_?NumericQ**b_]]:=a b;
HoldPattern[pProd[_,a_**b_?NumericQ]]:=a b;
HoldPattern[pProd[_,expr_]]:=Hold[expr];
(*pProdExpr has non-trivial code to deal with powers.*)
SetAttributes[pProdExpr,HoldAll];
HoldPattern[pProdExpr[x_^(m_Integer?Positive)]]:=
 With[{p=pProd[0,x**x]},
      p^Quotient[m,2]**x^Mod[m,2]/;p=!=Hold[x**x]&&p=!=x^2];
HoldPattern[pProdExpr[x_**(y:_Times|_NonCommutativeMultiply)]]:=
 With[{res=mark[x,pFactorList[y],False]//.mark[a_,{b_,c___},_]:>
  With[{p=pProdExpr[a**b]},mark[p,{c},True]/;p=!=Hold[a**b]]},
  res[[1]]**Head[y]@@res[[2]]/;res[[3]]];
HoldPattern[pProdExpr[x_NonCommutativeMultiply**y_]]:=
 With[{res=mark[pFactorList[x],y,False]//.mark[{a___,b_},c_,_]:>
  With[{p=pProdExpr[b**c]},mark[{a},p,True]/;p=!=Hold[b**c]]},
  NonCommutativeMultiply@@res[[1]]**res[[2]]/;res[[3]]];
HoldPattern[pProdExpr[x_Times**y_]]:=
 With[{res=mark[pFactorList[x],{}]
  //.mark[{a___,b_},{c___}]:>
   With[{p=pProdExpr[b**y]},Switch[p,
    b y|HoldPattern[y**b],mark[{a},{b,c}],(*Continue commuting y.*)
    Hold[b**y],With[
     {pos=-FirstPosition[Reverse[{c}],_?(pOrder[y,#1]=!=1&),{Length[{c}]+1},{1},Heads->False][[1]]},
     (*If y only commutes partway, place it according to pOrder:*)
     {Times@@{a,b,c}[[;;pos]]**Times@@{c,y}[[pos;;]],pos=!=-1}],
    _,{Times[a]**p**Times[c],True}]]
  /.mark[{},{c___}]:>{Times[y,c],True}},
  First[res]/;Last[res]];
HoldPattern[pProdExpr[x_^(m_:1)**x_^(n_:1)]]:=
 With[{l=m+n},
  If[IntegerQ[l]&&l>=2,
   With[{p=pProd[0,x**x]},
      If[p===Hold[x**x]||p===x^2,x^l,p^Quotient[l,2]**x^Mod[l,2]]],
   x^l]];
HoldPattern[pProdExpr[x_^(m_Integer:1)**y_^(n_Integer:1)/;m>=1&&n>=1]]:=
 With[{p=pProd[pOrder[x,y],x**y]},
  If[MatchQ[p,HoldPattern[y**x]|x y],x^m y^n,
   If[m===1,##&[],x^(m-1)]**p**If[n===1,##&[],y^(n-1)]
  ]/;p=!=Hold[x**y]];
HoldPattern[pProdExpr[expr_]]:=Hold[expr];
(*TODO: drop this def and simply leave pProdExpr unevaluated*)


(*Declaring products.*)
ClearAll[pRuleToSet];
pRuleToSet[Rule]:=Set;
pRuleToSet[RuleDelayed]:=SetDelayed;
ClearAll[pDeclareProduct];
SetAttributes[pDeclareProduct,HoldAll];
HoldPattern[pDeclareProduct[(rule:Rule|RuleDelayed)[lhs_,rhs_],always_]]:=
 With[{order=If[always,_,-1]},pRuleToSet[rule][HoldPattern[pProd[order,lhs]],rhs]];
Options[ADeclareProduct]={"Apply"->False};
SetAttributes[ADeclareProduct,HoldAll];
HoldPattern[ADeclareProduct[rules:((Rule|RuleDelayed)[_**_,_])...,OptionsPattern[]]]:=
 With[{always=OptionValue[Apply]},Scan[pDeclareProduct[#,always]&,Hold[rules]]];
(*Declaring commutators: some work needed to force x**y\[RuleDelayed]x*y when commutator evaluates to 0.*)
ClearAll[pDeclareCommutator];
SetAttributes[pDeclareCommutator,HoldAll];
HoldPattern[pDeclareCommutator[(rule:Rule|RuleDelayed)[{x_,y_},rhs_]]]:=
 (pRuleToSet[rule][HoldPattern[pProd[o_,(p:x)**(q:y)]],
   With[{r=rhs},If[r===0,p q,q**p+r]/;r===0||o===-1]];
  pRuleToSet[rule][HoldPattern[pProd[o_,(q:y)**(p:x)]],
   With[{r=rhs},If[r===0,p q,p**q-r]/;r===0||o===-1]];);
SetAttributes[ADeclareCommutator,HoldAll];
HoldPattern[ADeclareCommutator[rules:((Rule|RuleDelayed)[{_,_},_])...]]:=
 Scan[pDeclareCommutator,Hold[rules]];
(*Declaring anticommutator*)
ClearAll[pDeclareAnticommutator];
SetAttributes[pDeclareAnticommutator,HoldAll];
HoldPattern[pDeclareAnticommutator[(rule:Rule|RuleDelayed)[{x_,y_},rhs_],always_]]:=
 (pDeclareProduct[rule[(p:x)**(q:y),-q**p+rhs],False];
  pDeclareProduct[rule[(q:y)**(p:x),-p**q+rhs],False];
  pDeclareProduct[rule[(p:x)**(p:y),rhs/2],always];);
Options[ADeclareAnticommutator]={"Apply"->True};
SetAttributes[ADeclareAnticommutator,HoldAll];
HoldPattern[ADeclareAnticommutator[rules:((Rule|RuleDelayed)[{_,_},_])...,OptionsPattern[]]]:=
 With[{always=OptionValue[Apply]},Scan[pDeclareAnticommutator[#,always]&,Hold[rules]]];

(*pTmpPos[var] gives inverse map of the Order option of AExpand.
pOrder gives the current preferred order.*)
ClearAll[pTmpPos,pOrder];
HoldPattern[pTmpPos[_]]:=1;
HoldPattern[pOrder[Power[x_,n_],y_]]:=pOrder[x,y];
HoldPattern[pOrder[x_,Power[y_,n_]]]:=pOrder[x,y];
HoldPattern[pOrder[x:(_Plus|_Times|_NonCommutativeMultiply),y_]]:=
 pOrder[Hold@@x,y];
HoldPattern[pOrder[x_,y:(_Plus|_Times|_NonCommutativeMultiply)]]:=
 pOrder[x,Hold@@y];
HoldPattern[pOrder[x_Hold,y_Hold]]:=
 Order[0,Plus@@Flatten[Outer[pOrder,x,y]]];
HoldPattern[pOrder[x_Hold,y_]]:=pOrder[x,Hold[y]];
HoldPattern[pOrder[x_,y_Hold]]:=pOrder[Hold[x],y];
HoldPattern[pOrder[x_,y_]]:=
 Switch[Order[pTmpPos[x],pTmpPos[y]],1,1,-1,-1,_,AOrder[x,y]];

(*AExpand[expr, options___] or AExpand[options___][expr]
distributes and applies commutation/product rules.
Distribute\[Rule]patt only "distribute out" terms matching patt.
Expand\[Rule]patt uses (Expand[#,patt]&) instead of Expand.
Only\[Rule]patt only apply rules to factors matching patt.
Order\[Rule]{patt1,...} preferred order, _ is special, two _ is error.*)
SyntaxInformation[AExpand]={"ArgumentsPattern"->{_.,OptionsPattern[]}};
Options[AExpand]={"Distribute"->_,"Expand"->Sequence[],"Only"->_,"Order"->{_}};
HoldPattern[AExpand[expr___,opt:OptionsPattern[]]]:=
 With[{n=Length[{expr}],order=OptionValue["Order"]},
  If[n===0,
   AExpand[#1,opt,##2]&,
   Block[{pTmpPos},
    pTmpPos[_]=Length[order]+1;
    MapIndexed[(pTmpPos[#1]=First[#2])&,order];
    pTmpPos[_?NumericQ]=-1;
    distribute=OptionValue["Distribute"];
    expand=With[{e=OptionValue["Expand"]},Expand[#,e]&];
    only=OptionValue["Only"];
    pExpand[expr]
   ]]/;Which[
  n>1,Message[AExpand::argx,AExpand,n],
  Head[order]=!=List,Message[AExpand::badopt,Order->order],
  Count[order,Verbatim[_]]>=2,Message[AExpand::badopt,Order->order],
  True,True]]
distribute=_;
expand=Expand;
only=_;


(*pExpand*)
ClearAll[pExpand,pExpandTop,pExpandTimes,pExpandNcm];
HoldPattern[pExpand[arg:_NonCommutativeMultiply|_Times|_Power]]:=
 With[{dist=pDistribute[pExpandFactors[arg]]},
  If[Head[dist]===Plus,pExpand/@dist,pExpandTop[pFlattenProd[pSortFactors[dist]]]]];
(*TODO:optimize use of FixedPoint above.*)
HoldPattern[pExpand[arg:_List|_Plus|_And|_Nand|_Or|_Nor|_Xor|_Not|
  _Equal|_Less|_LessEqual|_Greater|_GreaterEqual]]:=pExpand/@arg;
HoldPattern[pExpand[arg_]]:=expand[arg];
ClearAll[pExpandFactors];
HoldPattern[pExpandFactors[arg:_NonCommutativeMultiply|_Times|_Power]]:=
 pExpandFactors/@arg;
HoldPattern[pExpandFactors[arg_]]:=pExpand[arg];
(*pDistribute[arg_] distributes NonCommutativeMultiply, Times and Power
immediately nested into each other starting at top-level (affected by
Distribute option).  In all cases, NonCommutativeMultiply is used in the
result because (a+b)**c\[Equal]c**(a+b) does not imply a**c\[Equal]c**a and b**c\[Equal]c**b.
However, if there was nothing to distribute the Times or Power are left
untouched.  E.g., a*b*(c+d)*e^2 becomes (a*b)**c**e^2+(a*b)**d**e^2.*)
ClearAll[pDistribute];
HoldPattern[pDistribute[arg_NonCommutativeMultiply]]:=
 Plus@@Flatten[Outer[NonCommutativeMultiply,
  Sequence@@List@@@pDistributeAux/@pDistribute/@List@@arg]];
HoldPattern[pDistribute[arg_Times]]:=
 Plus@@Flatten[Outer[NonCommutativeMultiply,
  Sequence@@List@@@(pDistributeAux/@pDistribute/@Sort[List@@arg,pOrder[#1,#2]>=0&]//.
   {a___,b_pNoDist,c__pNoDist,d___}:>{a,pNoDist[Times@@Join[b,c]],d})]];
HoldPattern[pDistribute[Power[x_,n_Integer?Positive]]]:=
 With[{ppd=pDistributeAux[pDistribute[x]]},
  Plus@@Flatten[Outer[NonCommutativeMultiply,
   Sequence@@ConstantArray[List@@ppd,n]]]/;Head[ppd]===pToDist];
HoldPattern[pDistribute[arg_]]:=arg;
(*pDistributeAux[arg] yields pToDist[term1,term2...] if the arg is a sum of
terms that should be distributed (according to the option Distribute) and
pNoDist[arg] otherwise.*)
ClearAll[pNoDist,pToDist,pDistributeAux];
HoldPattern[pDistributeAux[arg_Plus]]:=
 With[{assoc=GroupBy[List@@arg,FreeQ[distribute]]},
  With[{keep=Lookup[assoc,True,{}],dist=Lookup[assoc,False,{}]},
   With[{res=DeleteCases[Join[{Plus@@keep},dist],0]},
    If[Length[res]<=1,pNoDist,pToDist]@@res]]];
HoldPattern[pDistributeAux[arg_]]:=pNoDist[arg];

(*pSortFactors[arg_] finds Power, Times and NonCommutativeMultiply nested
in each other at top-level, turns Times into pTimes (to circumvent the
Orderless Attribute) and sorts its arguments according to pOrder.
It also turns NonCommutativeMultiply into pNonCommutativeMultiply.*)
ClearAll[pSortFactors];
HoldPattern[pSortFactors[arg_NonCommutativeMultiply]]:=
 pSortFactors/@pNonCommutativeMultiply@@arg;
HoldPattern[pSortFactors[arg_Power]]:=
 pSortFactors/@arg;
HoldPattern[pSortFactors[arg_Times]]:=
 Sort[pSortFactors/@pTimes@@arg,pOrder[#1,#2]>=0&]; (*TODO: we sort factors twice*)
HoldPattern[pSortFactors[arg_]]:=arg;
(*TODO: think whether pSortFactors should care about option Only.*)

(*pFlattenProd flattens product into pNonCommutativeMultiply[__pTimes] with
no further nesting.  Also integer powers into pTimes with repeated factors.*)
HoldPattern[pFlattenProd[arg_pNonCommutativeMultiply]]:=
 Join@@pFlattenProd/@arg;
HoldPattern[pFlattenProd[arg_pTimes]]:=
 mark[{},pFlattenProd/@List@@arg]//.
  mark[{a___},{b___,Longest[c:pNonCommutativeMultiply[_]..],d___}]:>
   mark[{a,b,pNonCommutativeMultiply[Join@@First/@{c}]},{d}]/.
  mark[{a___},{b___}]:>Join[a,b];
HoldPattern[pFlattenProd[Power[x_,n_Integer?Positive]]]:=
 If[Length[#]>1,
  Join@@ConstantArray[#,n],
  pNonCommutativeMultiply[Join@@ConstantArray[First[#],n]]]&[pFlattenProd[x]];
HoldPattern[pFlattenProd[arg_]]:=pNonCommutativeMultiply[pTimes[arg]];
(*TODO: implement negative powers:
(a**(y z))^-2\[Equal](z^-1 y^-1)**a^-1**(z^-1 y^-1)**a^-1*)

(*pExpandTop receives the result of pFlattenProd, after the argument
has been made a fixed point of pDistribute[pExpandFactors[#]]& and
has gone through pSortFactors.  Namely we now have
pNonCommutativeMultiply[__pTimes].  The goal is to apply pProd rules
to neighboring factors.*)
(*TODO: this code repeatedly tries the same transformations.  Optimze.*)
HoldPattern[pExpandTop[arg_pNonCommutativeMultiply]]:=
 mark[List@@arg,False]//.{
   mark[{a___,pTimes[b___,x_,y_,c___],d___},ch_]:>
    With[{p=pProdExpr[x**y]},
      mark[{a,pTimes[b,p,c],d},ch]/;Not[MatchQ[p,Hold[x**y]|Hold[y**x]|x y]]]
  }//.{
   mark[{a___,pTimes[b___,x_^(m_:1),x_^(n_:1),c___],d___},ch_]:>
    With[{l=m+n},If[l===0, mark[{a,pTimes[b,c],d},ch],
     mark[{a,pTimes[b,x^l,c],d},ch]]/;m n<=0],
   mark[a:{___,pTimes[],___},ch_]:>mark[DeleteCases[a,pTimes[]],ch],
   mark[{a___,b:pTimes[___,x:Except[_?(FreeQ[only])]],c:pTimes[y:Except[_?(FreeQ[only])],___],d___},ch_]:>
    With[{p=pProdExpr[x**y]},
     With[{res=
       Switch[p,
        Hold[x**y],Null,
        Hold[y**x]|x y,
         Which[
          AllTrue[Most[b],MatchQ[pProdExpr[#**y],Hold[y**#]|y #]&],
           mark[{a,
            Insert[b,y,-FirstPosition[Reverse[b],t_/;pOrder[t,y]===1,{-1},{1},Heads->False][[1]]],
            Rest[c],d},ch],(*
           mark[{a,Join[b,pTimes[y]],Rest[c],d},ch],*)
          pOrder[x,y]<0,
           mark[{a,Most[b],pTimes[y,x],Rest[c],d},True],
          True,Null],
        _,mark[{a,Most[b],pTimes[p],Rest[c],d},True]]},
      res/;res=!=Null]]
   }/.{
    mark[a_List,ch_]:>
     If[ch,pExpand,expand][
      pNonCommutativeMultiply@@a/.
       {pNonCommutativeMultiply->NonCommutativeMultiply,pTimes->Times}]};
HoldPattern[pExpandTop[arg_]]:=arg;
(*TODO: Rethink when little expand should be used.*)

(*pFactorList gives a list of factors, sorted by pOrder if the head is Times*)
ClearAll[pFactorList];
HoldPattern[pFactorList[arg_Times]]:=Sort[List@@arg,pOrder[#1,#2]>=0&];
HoldPattern[pFactorList[arg_NonCommutativeMultiply]]:=List@@arg;

(*(*pPrepDist[e1+e2+...] yields for instance pToDist[e3+e4+...,e1,e2,...],
where the first item is a sum of the terms free of the pattern distribute,
namely terms that should be kept together, and other terms are those that
should be distributed.*)
ClearAll[pPrepDist,pPrepFactorsDist];
HoldPattern[pPrepDist[expr_Plus]]:=
 With[{assoc=GroupBy[List@@expr,FreeQ[distribute]]},
  With[{keep=Lookup[assoc,True,{}],dist=Lookup[assoc,False,{}]},
   With[{res=DeleteCases[Join[{Plus@@keep},dist],0]},
    If[Length[res]<=1,pNoDist,pToDist]@@res]]];
HoldPattern[pPrepDist[expr_]]:=pNoDist[expr];
HoldPattern[pPrepFactorsDist[expr:_pTimes|_NonCommutativeMultiply|_Power]]:=
 pPrepFactorsDist/@expr;
HoldPattern[pPrepFactorsDist[expr_]]:=pPrepDist[expr];
*)
(*
(*pExpandTimes[arg_List, y_] gives pExpandTimes[result_List, True] or remains unevaluated.*)
HoldPattern[pExpandTimes[{a___,b:Except[_?(FreeQ[only])],c:Except[_?(FreeQ[only])],d___},_]]:=
 With[{prod=pProdExpr[b**c]},pExpandTimes[{a,prod,d},True]
/;prod=!=Hold[b**c]&&prod=!=b c];
(*pExpandNcm[arg_List, y_] gives pExpandNcm[result_List, True] or remains unevaluated.*)
HoldPattern[pExpandNcm[{a___,b:Except[_?(FreeQ[only])],c:Except[_?(FreeQ[only])],d___},_]]:=
 With[{prod=pProdExpr[b**c]},pExpandNcm[{a,prod,d},True]
  /;prod=!=Hold[b**c]];
*)

(*ACollect*)
ClearAll[pTermList,pToPattList,pCollectPre,pCollect,pCollectRight,pCollectLeft]
HoldPattern[pTermList[x_Plus]]:=List@@x;
HoldPattern[pTermList[x_]]:={x};
HoldPattern[pToPattList[p_]]:=
 If[MemberQ[#,Verbatim[_]],#,Join[#,{_}]]&[Flatten[{p}]];
SyntaxInformation[ACollect]={"ArgumentsPattern"->{_,_,_.,OptionsPattern[]}};
Options[ACollect]={"Distribute"->_,"Only"->_};
HoldPattern[ACollect[expr_,p_,h:Except[_List|_Rule|_RuleDelayed]:(#&),Longest[opts:OptionsPattern[]]]]:=
 With[{patts=pToPattList[p]},
  With[{expanded=AExpand[expr,FilterRules[{opts},Options[AExpand]],"Order"->patts]},
   pCollectPre[h,expanded,Sequence@@patts]]];
HoldPattern[pCollectPre[h_,expr:_List|_And|_Nand|_Or|_Nor|_Xor|_Not|_Equal|_Less|_LessEqual|_Greater|_GreaterEqual,patts___]]:=
 pCollectPre[h,#,patts]&/@expr;
HoldPattern[pCollectPre[h_,expr_,patts___]]:=
 Block[{pOrder=0&},AExpand[pCollect[h,pTermList[expr],patts],Distribute->Except[_],Expand->Except[_]]];
(*pCollect*)
HoldPattern[pCollect[h_,expr_List]]:=
 h[Plus@@expr];
HoldPattern[pCollect[h_,expr_List,Verbatim[_]]]:=
 h[Plus@@expr];
HoldPattern[pCollect[h_,expr_List,Verbatim[_],b___,c_]]:=
 Plus@@NonCommutativeMultiply@@@Reverse/@Normal@GroupBy[
  pCollectRight[#,c]&/@expr,
  Last->First,
  pCollect[h,pTermList[Total[#]],_,b]&];
HoldPattern[pCollect[h_,expr_List,a_,b___]]:=
 Plus@@NonCommutativeMultiply@@@Normal@GroupBy[
  pCollectLeft[#,a]&/@expr,
  First->Last,
  pCollect[h,pTermList[Total[#]],b]&];
(*pCollectLeft[expr,patt] yields {left,right} with left**right\[Equal]expr and left made of factors matching patt.*)
HoldPattern[pCollectLeft[expr_NonCommutativeMultiply,patt_]]:=
 Catch[Block[{left={}},
  Do[With[{col=pCollectLeft[expr[[i]],patt]},
   left={left,col[[1]]};
   If[col[[2]]=!=1,
   Throw[{NonCommutativeMultiply@@Flatten[left],
   NonCommutativeMultiply[col[[2]],expr[[i+1;;]]]},pCollect]]],
   {i,Length[expr]}]];{expr,1},pCollect];
HoldPattern[pCollectLeft[expr_Times,patt_]]:=
 Block[{left={},right={},done=False},
  Do[With[{col=pCollectLeft[x,patt]},
   Which[col[[2]]===1,left={left,x},
    done||col[[1]]===1,right={right,x},
    True,done=True;left={left,col[[1]]};right={right,col[[2]]}]],
   {x,List@@expr}];
  Times@@@Flatten/@{left,right}];
HoldPattern[pCollectLeft[expr:Power[x_,n_],patt_]]:=
 With[{col=pCollectLeft[x,patt]},
  Which[col[[2]]===1,{expr,1},
   col[[1]]=!=1&&IntegerQ[n]&&n>=1,{col[[1]],col[[2]]**x^(n-1)},
   True,{1,expr}]];
HoldPattern[pCollectLeft[expr_,patt_]]:=
 If[MatchQ[expr,patt],{expr,1},{1,expr}];
(*pCollectRight[expr,patt] yields {left,right} with left**right\[Equal]expr and right made of factors matching patt.*)
HoldPattern[pCollectRight[expr_NonCommutativeMultiply,patt_]]:=
 Catch[Block[{right={}},
  Do[With[{col=pCollectRight[expr[[i]],patt]},
   right={col[[2]],right};
   If[col[[1]]=!=1,
    Throw[{NonCommutativeMultiply[expr[[;;i-1]],col[[1]]],
     NonCommutativeMultiply@@Flatten[right]},pCollect]]],
   {i,Length[expr],1,-1}]];{1,expr},pCollect];
HoldPattern[pCollectRight[expr_Times,patt_]]:=
 Block[{left={},right={},done=False},
  Do[With[{col=pCollectRight[x,patt]},
    Which[col[[1]]===1,right={right,x},
     done||col[[2]]===1,left={left,x},
     True,done=True;left={left,col[[1]]};right={right,col[[2]]}]],
   {x,List@@expr}];
  Times@@@Flatten/@{left,right}];
HoldPattern[pCollectRight[expr:Power[x_,n_],patt_]]:=
 With[{col=pCollectRight[x,patt]},
  Which[col[[1]]===1,{1,expr},
   col[[2]]=!=1&&IntegerQ[n]&&n>=1,{x^(n-1)**col[[1]],col[[2]]},
   True,{expr,1}]];
HoldPattern[pCollectRight[expr_,patt_]]:=
 If[MatchQ[expr,patt],{1,expr},{expr,1}];

(*AMonomialRules*)
ClearAll[pMonomialsPre,pMonomials];
SyntaxInformation[AMonomialRules]={"ArgumentsPattern"->{_,_,_.,OptionsPattern[]}};
Options[AMonomialRules]={"Distribute"->_,"Only"->_};
HoldPattern[AMonomialRules[expr_,p_,h:Except[_List|_Rule|_RuleDelayed]:(#&),Longest[opts:OptionsPattern[]]]]:=
 With[{patts=pToPattList[p]},
  With[{expanded=AExpand[expr,FilterRules[{opts},Options[AExpand]],"Order"->patts]},
   pMonomialsPre[h,expanded,Sequence@@patts]]]
HoldPattern[pMonomialsPre[h_,expr:_List,patts___]]:=
 pMonomialsPre[h,#,patts]&/@expr;
HoldPattern[pMonomialsPre[h_,expr_,patts___]]:=
 pMonomials[h,pTermList[expr],patts];
(*pCoefficients*)
HoldPattern[pMonomials[h_,expr_List]]:=
 h[Plus@@expr];
HoldPattern[pMonomials[h_,expr_List,Verbatim[_]]]:=
 h[Plus@@expr];
HoldPattern[pMonomials[h_,expr_List,Verbatim[_],b___,c_]]:=
 GroupBy[
  pCollectRight[#,c]&/@expr,
  Last->First,
  pMonomials[h,pTermList[Total[#]],_,b]&];
HoldPattern[pMonomials[h_,expr_List,a_,b___]]:=
 GroupBy[
  pCollectLeft[#,a]&/@expr,
  First->Last,
  pMonomials[h,pTermList[Total[#]],b]&];

(*AValidate*)
SyntaxInformation[AValidate]={"ArgumentsPattern"->{_}};
SetArgumentCount[AValidate,1]
SetAttributes[AValidate,HoldAll]
HoldPattern[AValidate[expr_Times]]:=
 And@@(AExpand[#1**#2]===AExpand[#2**#1]&)@@@Subsets[List@@expr,{2}];
HoldPattern[AValidate[expr_?AtomQ]]:=True;
HoldPattern[AValidate[expr_]]:=And@@Map[AValidate,List@@expr];

(*pExprQ detects some common expressions to prevent them from being used as variables*)
ClearAll[pExprQ,pScalarQ];
HoldPattern[pExprQ[_Plus|_Times|_NonCommutativeMultiply|_Power]]:=True;
HoldPattern[pExprQ[_]]:=False;
(*pScalarQ detects expressions involving only scalars*)
HoldPattern[pScalarQ[_?NumericQ]]:=True;
HoldPattern[pScalarQ[x:_Plus|_Times|_NonCommutativeMultiply|_Power]]:=AllTrue[x,pScalarQ];
HoldPattern[pScalarQ[x_]]:=(AClass[x]==="scalar");
(*PartialD*)
HoldPattern[PartialD[]]:=1;
HoldPattern[PartialD[var_]/;
 If[pExprQ[var]||NumericQ[var],
  Message[PartialD::notvar,var]]]:=Null;
ADeclareProduct[
 (x_?pScalarQ)**(y_?pScalarQ):>x y,
 PartialD[x_?pScalarQ]**PartialD[y_?pScalarQ]:>PartialD[x]PartialD[y],
 (x_?pScalarQ)**(y_?(FreeQ[_?(AOfClassQ["differential"])])):>x y,
 (y_?(FreeQ[_?(AOfClassQ["differential"])]))**(x_?pScalarQ):>x y,
 Apply->True];
ADeclareCommutator[{PartialD[x_?(AOfClassQ["scalar"])],(y_?pScalarQ)}:>D[y, x]];
HoldPattern[PartialD[a_?pScalarQ,b__?pScalarQ]]:=Times@@PartialD/@Hold[a,b];
HoldPattern[PartialD[a_,b__]]:=NonCommutativeMultiply@@PartialD/@Hold[a,b];

(*Messages*)
PartialD::notvar="PartialD expects one or more variables as its arguments, not the expression or number `1`.";
AClass::unknown="The class `1` was not declared.";
AExpand::badopt="Option `1` for AExpand is invalid."; 
AOfClassQ::pattx="AOfClassQ used as \"?AOfClassQ[...]\" instead of \"?(AOfClassQ[...])\".";

(HoldPattern[#[___]]:=RuleCondition[Message[#::usage];Fail])&/@{
  ACollect,
  AMonomialRules,
  ADeclareProduct,
  ADeclareCommutator,
  ADeclareAnticommutator};

Protect@@allfunctions;
Protect[NonCommutativeMultiply];
Unprotect[AClass];

End[];
EndPackage[];
"The AAlgebra package provides the commands AExpand, ACollect, AMonomialRules, \
AValidate, AClass, AOfClassQ, AOrder, AClassOrder, AOrderWithinClass, \
ADeclareProduct, ADeclareCommutator, ADeclareAnticommutator, PartialD, $AMaxPower"
