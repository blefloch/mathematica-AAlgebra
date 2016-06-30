(* ::Package:: *)

BeginPackage["SSAlgebra`",{"Macros`"}];
`Private`allfunctions=Hold[
 NonCommutativeMultiply,
 SSExpand,
 SSCollect,
 SSMonomials,
 SSValidate,
 SSClass,
 SSOfClassQ,
 SSOrder,
 SSClassOrder,
 SSOrderWithinClass,
 SSDeclareProduct,
 SSDeclareCommutator,
 SSDeclareAnticommutator,
 PartialD,
 $SSMaxPower
];

Begin["`Private`"];

Unprotect@@allfunctions;
ClearAll@@allfunctions;

(*TODO: in SSMonomials, sort the association by exponent*)
(*TODO: maybe only look for commutativity (hence ugly brackets) in terms with only two factors and in factors of same class?*)
(*TODO: in SSExpand, build a more clever order.*)
(*TODO: in SSCollect and SSMonomials, build a more clever order for SSExpand,
as the current one breaks with e.g. patt={x,_,x}.*)
(*TODO: document and implement SSCollect[expr,{x1,{{x2,{_,y2}},y1}}] for
nested collection with more control on the left/right order.*)
(*TODO: write proper documentation pages, shorten usage strings.*)
(*TODO: the final SSExpand in SSCollect is a bit too eager and may send a(b**c) to (ab)**c when we try to collect {_,b|c}.*)

(*Usage["The expression $a/b+a/b$ is equal to $2a/b$"] will pretty-print
what's between dollars.*)
HoldPattern[Usage[str_]]:=
StringReplace[str,"$"~~Shortest[a___]~~"$":>
  With[{expr=MakeExpression[a,StandardForm]/.HoldComplete->HoldForm},
       If[Head[expr]===ErrorBox,a,
          "\*"<>ToString[ToBoxes[
            expr/.x_Symbol:>With[{y=If[LowerCaseQ[ToString[x]],Style[x,"TI"],x]},y/;True],
            StandardForm],InputForm]]]];

SSExpand::usage=Usage@"\
$SSExpand[expr, options]$ or equivalently $SSExpand[options][expr]$ \
distributes non-commutative products and applies commutation rules and product \
rules (see $SSDeclareAnticommutator$, $SSDeclareCommutator$, $SSDeclareProduct$) in \
an effort to order factors according to the preferred order (see $SSOrder$).

The product is assumed to be associative: when evaluating $a**b**c$ there is no \
guarantee on whether a rule for $a**b$ or for $b**c$ will apply first. \

The function $Expand$ is applied where relevant.  Just like $Expand$, $SSExpand$ \
threads over lists, equations, inequalities and logic functions.

$Distribute->patt$ prevents $SSExpand$ from distributing terms free of $patt$: if \
$a$ and $b$ match $patt$ and $x$ and $y$ do not then $(x+y+a+b^2)**(x+y+b)$ becomes \
$(x+y)^2+(x+y)**b+a**(x+y)+a**b+b^2**(x+y)+b^3$.

$Only->patt$ prevents $SSExpand$ from applying commutation and product rules for \
factors free of $patt$.  A useful pattern is $_?(SSOfClassQ[class])$.

$Order->{x,y...}$ causes $SSExpand$ to use as the preferred order the order \
where variables matching $x$ are placed to the left of those matching $y$, \
and so on, ending with variables that match none of the patterns.  Variables \
matching the same pattern are ordered according to the default order $SSOrder$. \
The pattern $_$ is treated specially: it only matches if no other pattern \
matches (using $_$ twice is an error).  If a variable matches several \
patterns there is no guarantee on which one matches.

$Expand->patt$ causes $SSExpand$ to apply $Expand[#,patt]&$ instead of \
$Expand$.  To disable $Expand$ completely use the pattern $Except[_]$.";

SSCollect::usage=Usage@"\
$SSCollect[expr, x]$ expands $expr$ using $SSExpand$ then collects together \
terms with the same power of (any variable matching) $x$.  The $x$ are factored \
towards the left of the expression.

$SSCollect[expr, {x1, x2..., _..., y2, y1}]$ expands $expr$ using $SSExpand$, \
then collects terms according to the powers of (variables matching) $x1$, and \
in each coefficient collects terms according to the powers of $x2$, and so \
on until reaching the general pattern $_$ in the pattern list.  Then powers \
of $y1$ are collected to the right, and in each coefficient powers of $y2$, \
and so on.

$SSCollect[expr, vars, h]$ applies $h$ to each coefficient.

$Distribute->patt$ and $Only->patt$ are passed to $SSExpand$ as options.  Just \
like $SSExpand$, $SSCollect$ threads over lists, equations, inequalities and \
logic functions.";

SSMonomials::usage=Usage@"\
$SSMonomials[expr, x]$ expands $expr$ and collects terms according to the \
power of (any variable matching) $x$ to the left of the expression.  The \
result is given as an association whose keys are products of variables $x$ \
and whose values are the corresponding coefficients.

$SSMonomials[expr, {x1, x2..., _..., y2, y1}]$ gives nested associations \
whose keys are products of variables matching $x1$, then $x2$ and so on, \
then $y1$, $y2$, and so on.  The syntax is the same as $SSCollect$.

$SSMonomials[expr, vars, h]$ applies $h$ to each coefficient.

$Distribute->patt$ and $Only->patt$ are passed to $SSExpand$ as options.  \
$SSMonomials$ threads over lists in $expr$.";

SSValidate::usage=Usage@"\
$SSValidate[expr]$ checks that usual (commutative) multiplication is only used \
in $expr$ with factors that commute.  If yes, it yields True, otherwise False. \
Other validation steps might be added in the future.";

SSClass::usage=Usage@"\
$SSClass[var]$ gives the class of $var$.  The class of a variable affects the \
preferred ordering in products.  It is declared in the same way as usual \
functions, namely $SSClass[patt_]:=c$ declares that variables matching the pattern \
$patt$ have class $c$.  This declaration also adds $c$ (if it is new) to the list of \
classes, whose order defines the default ordering of classes.

The class \"number\" is predefined and it includes $NumericQ$ quantities. \
A non-commutative product with a variable of this class is automatically \
converted to a commutative product.

The class \"scalar\" is predefined for variables that commute with all others \
except those of class \"differential\" (see below).  Declaring that $x$ is a \
scalar is done with $SSClass[x]:=\"scalar\"$.

The class \"differential\" is predefined for differential operators.  It \
includes $PartialD[x]$ (see $PartialD$).";

SSOfClassQ::usage=Usage@"\
$SSOfClassQ[patt][var]$ is $True$ if $SSClass[var]$ matches the pattern $patt$. \
Thus, the pattern $_?(SSOfClassQ[patt])$ matches members of any class \
matched by $patt$.";

SSOrder::usage=Usage@"\
$SSOrder[x, y]$ indicates the preferred order of the variables $x$ and $y$ in \
non-commutative products, to determine whether applicable commutation rules \
should be used.  It is $1$ if $x**y$ is preferred, $-1$ if $y**x$ is, and $0$ if $x===y$. \
It is important that $SSOrder[x, y] == -SSOrder[y, x]$.

The default order relies on comparing the variables' classes $SSClass[x]$ and \
$SSClass[y]$ using $SSClassOrder$.  If this gives $0$ (for instance if $x$ and $y$ have \
the same class) then $x$ and $y$ are compared using $SSOrderWithinClass$, typically \
the standard $Order$.";

SSClassOrder::usage=Usage@"\
$SSClassOrder[c, d]$ gives $1$ if variables of class $c$ should be ordered before \
those of class $d$ in non-commutative products (using available commutation rules), \
$-1$ if they should be ordered after, and $0$ if the order is indifferent.  In this \
last case (including the case $c===d$), $SSOrderWithinClass$ is used to determine \
the order.  It is important that $SSClassOrder[d, c] == -SSClassOrder[c, d]$.

By default, $SSClassOrder$ is the order in which classes are declared using \
$SSClass[patt]:=c$, except for the class \"differential\" which is placed to the \
very right.";

SSOrderWithinClass::usage=Usage@"\
$SSOrderWithinClass[x, y, classx, classy]$ is used to determine the preferred \
order $SSOrder[x, y]$ of $x$ and $y$ when comparing their classes is not enough \
(when $SSClassOrder$ gives $0$).  By default this is the standard $Order[x, y]$.

The classes of $x$ and $y$ are included here among the arguments so that one can \
more easily defined a custom order for variables of a specific class.  It is \
important that $SSOrderWithinClass[y, x, classy, classx] == \
-SSOrderWithinClass[x, y, classx, classy]$.";

SSDeclareProduct::usage=Usage@"\
$SSDeclareProduct[x**y :> rhs...]$ declares one or more rules for the \
product of two variables (or patterns), namely it declares $x**y$ equal to $rhs$. \
A condition can be included in the $rhs$: $SSDeclareProduct[x**y:>expr/;cond]$. \
By default, this rule is only used by $SSExpand$ if $x$ and $y$ are not in the \
preferred order.

$Apply->True$ causes the rules being declared to be applied even if $x**y$ is \
already in the preferred order (including the case where they coincide). \
This may lead to infinite recursion if the right-hand side involves $y**x$.";

SSDeclareCommutator::usage=Usage@"\
$SSDeclareCommutator[{x,y} :> rhs...]$ declares one or more rules for the \
commutator of two variables (or patterns), namely it declares $x**y$ equal to \
$y**x+rhs$ (and conversely $y**x$ equal to $x**y-rhs$).  This rule is used by \
$SSExpand$ to bring products in the preferred order.";

SSDeclareAnticommutator::usage=Usage@"\
$SSDeclareAnticommutator[{x,y} :> rhs...]$ declares one or more rules for \
the anticommutator of two variables (or patterns), namely it declares $x**y$ \
equal to $-y**x+rhs$ (and conversely $y**x$ equal to $-x**y+rhs$).  It also takes \
care of the case where $x$ and $y$ are equal: $x**x$ is declared to be $rhs/2$.  This \
rule is used by $SSExpand$ to bring products in the preferred order.";

PartialD::usage=Usage@"\
$PartialD[x_]$ represents the partial derivative operator with respect to the \
(scalar) variable $x$.  In products, it can be commuted through any \
expression using $PartialD[x]**y - y**PartialD[x] == D[y, x]$.";

$SSMaxPower=100;

(*Before declaring any global rule which involves NonCommutativeMultiply we made sure to remove its attributes Flat and OneIdentity by running ClearAll[NonCommutativeMultiply].
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



(*SSClass[var] user-defined class of var.
pClassPos[class] helps control the preferred order.
pClassQ[str_String] is True if str is a class name.*)
ClearAll[pClassQ,pClassPos];
pClassQ[class_String]:=(Head[pClassPos[class]]=!=pClassPos);
SyntaxInformation[SSClass]={"ArgumentsPattern"->{_}};
SetArgumentCount[SSClass,1];
plastcp=0;
SSClass/:HoldPattern[(Set|SetDelayed|TagSet|TagSetDelayed)
  [___,SSClass[___],class_String]/;
  If[Not[pClassQ[class]],pClassPos[class]=(plastcp+=10)]]:=Null;
SSClass[_?NumericQ]:="number";
SSClass[]:="scalar";SSClass[]=.;(*Kludge to declare class "scalar" with right priority.*)
SSClass[PartialD[_]]:="differential";
pClassPos["differential"]=100000;

(*SSOfClassQ[class_][var_]*)
SyntaxInformation[SSOfClassQ]={"ArgumentsPattern"->{_}};
SetArgumentCount[SSOfClassQ,1];
SSOfClassQ/:HoldPattern[Verbatim[PatternTest][_,SSOfClassQ]]:=
 Null/;Message[SSOfClassQ::pattx];
HoldPattern[SSOfClassQ[class_String]/;
 If[Not[pClassQ[class]],Message[SSClass::unknown,class]]]:=Null;
HoldPattern[SSOfClassQ[class_]]:=(MatchQ[SSClass[#],class]&);

(*SSOrder[x, y] in terms of SSClassOrder[c, d] and SSOrderWithinClass[x, y, c, d]*)
SyntaxInformation[SSOrder]={"ArgumentsPattern"->{_,_}};
SetArgumentCount[SSOrder,2];
HoldPattern[SSOrder[x_, y_]]:=
 With[{cx=SSClass[x],cy=SSClass[y]},
      Switch[SSClassOrder[cx,cy],1,1,-1,-1,
             _,SSOrderWithinClass[x,y,cx,cy]]];
SyntaxInformation[SSClassOrder]={"ArgumentsPattern"->{_,_}};
SetArgumentCount[SSClassOrder,2];
HoldPattern[SSClassOrder[c_String?pClassQ,d_String?pClassQ]]:=
 If[pClassQ[c]&&pClassQ[d],Order[pClassPos[c],pClassPos[d]],0];
SyntaxInformation[SSOrderWithinClass]={"ArgumentsPattern"->{_,_,_,_}};
SetArgumentCount[SSOrderWithinClass,4];
HoldPattern[SSOrderWithinClass[x_,y_,_,_]]:=Order[x,y];

(*Second argument of pProd is of the form x**y.
First argument of pProd gives pOrder[x, y], fewer rules apply when that is -1.*)
ClearAll[pProd,pProdExpr];
SetAttributes[pProd,HoldRest];
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
     {Times@@{a,b,c}[[;;pos]]**Times@@{c,y}[[pos;;]],pos=!=-1}], (*If y only commutes partway, place it according to pOrder.*)
    _,{Times[a]**p**Times[c],True}]]
  /.mark[{},{c___}]:>{Times[y,c],True}},
  First[res]/;Last[res]];
HoldPattern[pProdExpr[x_^(m_:1)**x_^(n_:1)]]:=
 With[{l=m+n},x^l];
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
Options[SSDeclareProduct]={"Apply"->False};
SetAttributes[SSDeclareProduct,HoldAll];
HoldPattern[SSDeclareProduct[rules:((Rule|RuleDelayed)[_**_,_])...,OptionsPattern[]]]:=
 With[{always=OptionValue[Apply]},Scan[pDeclareProduct[#,always]&,Hold[rules]]];
(*Declaring commutators: some work needed to force x**y\[RuleDelayed]x*y when commutator evaluates to 0.*)
ClearAll[pDeclareCommutator];
SetAttributes[pDeclareCommutator,HoldAll];
HoldPattern[pDeclareCommutator[(rule:Rule|RuleDelayed)[{x_,y_},rhs_]]]:=
 (pRuleToSet[rule][HoldPattern[pProd[o_,(p:x)**(q:y)]],
   With[{r=rhs},If[r===0,p q,q**p+r]/;r===0||o===-1]];
  pRuleToSet[rule][HoldPattern[pProd[o_,(q:y)**(p:x)]],
   With[{r=rhs},If[r===0,p q,p**q-r]/;r===0||o===-1]];);
SetAttributes[SSDeclareCommutator,HoldAll];
HoldPattern[SSDeclareCommutator[rules:((Rule|RuleDelayed)[{_,_},_])...]]:=
 Scan[pDeclareCommutator,Hold[rules]];
(*Declaring anticommutator*)
ClearAll[pDeclareAnticommutator];
SetAttributes[pDeclareAnticommutator,HoldAll];
HoldPattern[pDeclareAnticommutator[(rule:Rule|RuleDelayed)[{x_,y_},rhs_],always_]]:=
 (pDeclareProduct[rule[(p:x)**(q:y),-q**p+rhs],False];
  pDeclareProduct[rule[(q:y)**(p:x),-p**q+rhs],False];
  pDeclareProduct[rule[(p:x)**(p:y),rhs/2],always];);
Options[SSDeclareAnticommutator]={"Apply"->True};
SetAttributes[SSDeclareAnticommutator,HoldAll];
HoldPattern[SSDeclareAnticommutator[rules:((Rule|RuleDelayed)[{_,_},_])...,OptionsPattern[]]]:=
 With[{always=OptionValue[Apply]},Scan[pDeclareAnticommutator[#,always]&,Hold[rules]]];

(*pTmpPos[var] gives inverse map of the Order option of SSExpand.
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
 Switch[Order[pTmpPos[x],pTmpPos[y]],1,1,-1,-1,_,SSOrder[x,y]];

(*SSExpand[expr, options___] or SSExpand[options___][expr]
distributes and applies commutation/product rules.
Distribute\[Rule]patt only "distribute out" terms matching patt.
Expand\[Rule]patt uses (Expand[#,patt]&) instead of Expand.
Only\[Rule]patt only apply rules to factors matching patt.
Order\[Rule]{patt1,...} preferred order, _ is special, two _ is error.*)
SyntaxInformation[SSExpand]={"ArgumentsPattern"->{_.,OptionsPattern[]}};
Options[SSExpand]={"Distribute"->_,"Expand"->Sequence[],"Only"->_,"Order"->{_}};
HoldPattern[SSExpand[expr___,opt:OptionsPattern[]]]:=
 With[{n=Length[{expr}],order=OptionValue["Order"]},
  If[n===0,
   SSExpand[#1,opt,##2]&,
   Block[{pTmpPos},
    pTmpPos[_]=Length[order]+1;
    MapIndexed[(pTmpPos[#1]=First[#2])&,order];
    distribute=OptionValue["Distribute"];
    expand=With[{e=OptionValue["Expand"]},Expand[#,e]&];
    only=OptionValue["Only"];
    pExpand[expr]
   ]]/;Which[
  n>1,Message[SSExpand::argx,SSExpand,n],
  Head[order]=!=List,Message[SSExpand::badopt,Order->order],
  Count[order,Verbatim[_]]>=2,Message[SSExpand::badopt,Order->order],
  True,True]]
distribute=_;
expand=Expand;
only=_;

(*pPrepDist[e1+e2+...] yields for instance {e3+e4+...,e1,e2,...},
where the first item is a sum of the terms free of the pattern distribute,
namely terms that should be kept together, and other terms are those that
should be distributed.*)
ClearAll[pPrepDist,pDistribute];
HoldPattern[pPrepDist[expr_Plus]]:=
 With[{assoc=GroupBy[List@@expr,FreeQ[distribute]]},
  With[{keep=Lookup[assoc,True,{}],dist=Lookup[assoc,False,{}]},
   DeleteCases[Join[{Plus@@keep},dist],0]]];
HoldPattern[pPrepDist[expr_]]:={expr};
(*pDistribute[(a+b)**(c+d)] gives a**c+b**c+a**d+b**d (affected by Distribute option).*)
HoldPattern[pDistribute[arg_NonCommutativeMultiply]]:=
 Plus@@Flatten[Outer[NonCommutativeMultiply,
  Sequence@@pPrepDist/@pFactorList[arg]]];
(*pFactorList gives a list of factors, sorted by pOrder if the head is Times*)
ClearAll[pFactorList];
HoldPattern[pFactorList[arg_Times]]:=Sort[List@@arg,pOrder[#1,#2]>=0&];
HoldPattern[pFactorList[arg_NonCommutativeMultiply]]:=List@@arg;
(*pExpand*)
ClearAll[pExpand,pExpandShallow,pExpandTimes,pExpandNcm];
HoldPattern[pExpand[arg:_List|_Plus|_And|_Nand|_Or|_Nor|_Xor|_Not|
  _Equal|_Less|_LessEqual|_Greater|_GreaterEqual]]:=pExpand/@arg;
HoldPattern[pExpand[arg:_Times|_NonCommutativeMultiply|_Power]]:=
 pExpandShallow[pExpand/@arg];
HoldPattern[pExpand[arg_]]:=expand[arg];
(*pExpandShallow receives its argument after subparts have been through pExpand.
The head may differ from the original argument of pExpand, due to evaluation.*)
HoldPattern[pExpandShallow[arg_Times]]:=
 With[{ppd=pPrepDist/@pFactorList[arg]},
  If[MemberQ[ppd,{_,__}],
   pExpand[Plus@@Flatten[Outer[NonCommutativeMultiply,
    {Times@@Flatten[Cases[ppd,{_}]]},
    Sequence@@DeleteCases[ppd,{_}]]]],
   (If[#2,pExpand,expand][Times@@#1]&)@@pExpandTimes[Flatten[ppd],False]]];
HoldPattern[pExpandShallow[arg_NonCommutativeMultiply]]:=
 With[{expr=pDistribute[arg]},
  Switch[Head[expr],
   Plus|Power|Times,pExpand[expr],
   NonCommutativeMultiply,
   (If[#2,pExpand,expand][NonCommutativeMultiply@@#1]&)@@pExpandNcm[List@@expr,False]
  ]];
HoldPattern[pExpandShallow[Power[y_/;Not[NumericQ[y]],n_Integer?Positive]]]:=
 With[{zlist=pPrepDist[y]},
  If[Length[zlist]=!=1,
   pExpand[Plus@@Flatten[Outer[NonCommutativeMultiply,Sequence@@Table[zlist,{n}]]]],
   With[{z=First[zlist]},
    If[Head[z]=!=Times&&Head[z]=!=NonCommutativeMultiply,
     With[{zn=pProdExpr[z^n]},If[zn===Hold[z^n],z^n,pExpand[zn]]],
     With[{zf=pFactorList[z]},
      If[#2,First[zf]**Sequence@@Flatten[Table[{Rest[zf],#1},{n-1}]]**Rest[zf],z^n]&@@
pExpandNcm[{Last[zf],First[zf]},False]]]]]];
HoldPattern[pExpandShallow[arg_Power]]:=expand[arg];
HoldPattern[pExpandShallow[arg_]]:=pExpand[arg];
(*pExpandTimes[arg_List, y_] gives pExpandTimes[result_List, True] or remains unevaluated.*)
HoldPattern[pExpandTimes[{a___,b:Except[_?(FreeQ[only])],c:Except[_?(FreeQ[only])],d___},_]]:=
 With[{prod=pProdExpr[b**c]},pExpandTimes[{a,prod,d},True]
/;prod=!=Hold[b**c]&&prod=!=b c];
(*pExpandNcm[arg_List, y_] gives pExpandNcm[result_List, True] or remains unevaluated.*)
HoldPattern[pExpandNcm[{a___,b:Except[_?(FreeQ[only])],c:Except[_?(FreeQ[only])],d___},_]]:=
 With[{prod=pProdExpr[b**c]},pExpandNcm[{a,prod,d},True]
  /;prod=!=Hold[b**c]];

(*SSCollect*)
ClearAll[pTermList,pToPattList,pCollectPre,pCollect,pCollectRight,pCollectLeft]
HoldPattern[pTermList[x_Plus]]:=List@@x;
HoldPattern[pTermList[x_]]:={x};
HoldPattern[pToPattList[p_]]:=
 If[MemberQ[#,Verbatim[_]],#,Join[#,{_}]]&[Flatten[{p}]];
SyntaxInformation[SSCollect]={"ArgumentsPattern"->{_,_,_.,OptionsPattern[]}};
Options[SSCollect]={"Distribute"->_,"Only"->_};
HoldPattern[SSCollect[expr_,p_,h:Except[_List|_Rule|_RuleDelayed]:(#&),Longest[opts:OptionsPattern[]]]]:=
 With[{patts=pToPattList[p]},
  With[{expanded=SSExpand[expr,FilterRules[{opts},Options[SSExpand]],"Order"->patts]},
   pCollectPre[h,expanded,Sequence@@patts]]];
HoldPattern[pCollectPre[h_,expr:_List|_And|_Nand|_Or|_Nor|_Xor|_Not|_Equal|_Less|_LessEqual|_Greater|_GreaterEqual,patts___]]:=
 pCollectPre[h,#,patts]&/@expr;
HoldPattern[pCollectPre[h_,expr_,patts___]]:=
 Block[{pOrder=0&},SSExpand[pCollect[h,pTermList[expr],patts],Distribute->Except[_],Expand->Except[_]]];
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

(*SSMonomials*)
ClearAll[pMonomialsPre,pMonomials];
SyntaxInformation[SSMonomials]={"ArgumentsPattern"->{_,_,_.,OptionsPattern[]}};
Options[SSMonomials]={"Distribute"->_,"Only"->_};
HoldPattern[SSMonomials[expr_,p_,h:Except[_List|_Rule|_RuleDelayed]:(#&),Longest[opts:OptionsPattern[]]]]:=
 With[{patts=pToPattList[p]},
  With[{expanded=SSExpand[expr,FilterRules[{opts},Options[SSExpand]],"Order"->patts]},
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

(*SSValidate*)
SyntaxInformation[SSValidate]={"ArgumentsPattern"->{_}};
SetArgumentCount[SSValidate,1]
SetAttributes[SSValidate,HoldAll]
HoldPattern[SSValidate[expr_Times]]:=
 And@@(SSExpand[#1**#2]===SSExpand[#2**#1]&)@@@Subsets[List@@expr,{2}];
HoldPattern[SSValidate[expr_?AtomQ]]:=True;
HoldPattern[SSValidate[expr_]]:=And@@Map[SSValidate,List@@expr];

(*pExprQ detects some common expressions to prevent them from being used as variables*)
ClearAll[pExprQ,pScalarQ];
HoldPattern[pExprQ[_Plus|_Times|_NonCommutativeMultiply|_Power]]:=True;
HoldPattern[pExprQ[_]]:=False;
(*pScalarQ detects expressions involving only scalars*)
HoldPattern[pScalarQ[_?NumericQ]]:=True;
HoldPattern[pScalarQ[x:_Plus|_Times|_NonCommutativeMultiply|_Power]]:=AllTrue[x,pScalarQ];
HoldPattern[pScalarQ[x_]]:=(SSClass[x]==="scalar");
(*PartialD*)
HoldPattern[PartialD[]]:=1;
HoldPattern[PartialD[var_]/;
 If[pExprQ[var]||NumericQ[var],
  Message[PartialD::notvar,var]]]:=Null;
SSDeclareProduct[
 (x_?pScalarQ)**(y_?pScalarQ):>x y,
 PartialD[x_?pScalarQ]**PartialD[y_?pScalarQ]:>PartialD[x]PartialD[y],
 (x_?pScalarQ)**(y_?(FreeQ[_?(SSOfClassQ["differential"])])):>x y,
 (y_?(FreeQ[_?(SSOfClassQ["differential"])]))**(x_?pScalarQ):>x y,
 Apply->True];
SSDeclareCommutator[{PartialD[x_?(SSOfClassQ["scalar"])],(y_?pScalarQ)}:>D[y, x]];
HoldPattern[PartialD[a_?pScalarQ,b__?pScalarQ]]:=Times@@PartialD/@Hold[a,b];
HoldPattern[PartialD[a_,b__]]:=NonCommutativeMultiply@@PartialD/@Hold[a,b];

(*Messages*)
PartialD::notvar="PartialD expects one or more variables as its arguments, not the expression or number `1`.";
SSClass::unknown="The class `1` was not declared.";
SSExpand::badopt="Option `1` for SSExpand is invalid."; 
SSOfClassQ::pattx="SSOfClassQ used as \"?SSOfClassQ[...]\" instead of \"?(SSOfClassQ[...])\".";

Protect@@allfunctions;
Protect[NonCommutativeMultiply];
Unprotect[SSClass];

End[];
EndPackage[];
"The SSAlgebra package provides the commands SSExpand, SSCollect, SSMonomials, \
SSValidate, SSClass, SSOfClassQ, SSOrder, SSClassOrder, SSOrderWithinClass, \
SSDeclareProduct, SSDeclareCommutator, SSDeclareAnticommutator, PartialD, $SSMaxPower"
