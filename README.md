# mathematica-SSAlgebra
Mathematica package to compute with custom products and (anti)commutators

Install by putting `SSAlgebra.wl` in the right place.

    <<Get["SSAlgebra`"]
    SSClass[x]="scalar";
    SSExpand[PartialD[x]**x^2]

>       2x + x^2**PartialD[x]

    SSExpand[a**(b+c)**b]

>       a**b^2 + a**c**b

    SSClass[a]="scalar";
    SSClass[b]="scalar";
    SSExpand[a**(b+c)**b]

>       a b^2 + a b c

We can use the package to compute in Uq(sl2), for instance checking some calculations in math/0507477.

    SSClass[q] = "scalar";
    SSDeclareCommutator[{e, f} :> (k - k^-1)/(q - q^-1)];
    SSDeclareProduct[
      k ** e :> q^2 e ** k,
      k ** f :> q^-2 f ** k,
      (k^-1) ** e :> q^-2 e ** (k^-1),
      (k^-1) ** f :> q^2 f ** (k^-1)
    ];
    rules = {
      x -> k,
      y -> k^-1 + (q - q^-1) f,
      z -> k^-1 - (k^-1) ** e (q^2 - 1)
    };
    SSExpand[q x ** y - q^-1 y ** x == q - q^-1 /. rules] // Simplify
    SSExpand[q y ** z - q^-1 z ** y == q - q^-1 /. rules] // Simplify
    SSExpand[q z ** x - q^-1 x ** z == q - q^-1 /. rules] // Simplify

>       True
>       True
>       True
