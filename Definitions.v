Require Import Kami.All.

Notation NatToWord sz x := (natToWord sz x).

Section Definitions.
  Variable expWidthMinus2 sigWidthMinus2: nat.
  
  Local Notation expWidthMinus1 := (expWidthMinus2 + 1).
  Local Notation expWidth := (expWidthMinus1 + 1).

  Local Notation sigWidthMinus1 := (sigWidthMinus2 + 1).
  Local Notation sigWidth := (sigWidthMinus1 + 1).

  Definition FN :=
    STRUCT_TYPE {
        "sign" :: Bool;
        "exp" :: Bit expWidth;
        "frac" :: Bit sigWidthMinus1
      }.

  Definition RawFloat :=
    STRUCT_TYPE {
        "isNaN" :: Bool;
        "isInf" :: Bool;
        "isZero" :: Bool;
        "sign" :: Bool;
        "sExp" :: Bit (expWidth + 1);
        "sig" :: Bit sigWidthMinus1
      }.

  Definition RecFN :=
    STRUCT_TYPE {
        "sign" :: Bool;
        "isZeroNaNInf0" :: Bit 1;
        "isZeroNaNInf1" :: Bit 1;
        "isZeroNaNInf2" :: Bit 1;
        "exp" :: Bit expWidthMinus2;
        "fract" :: Bit sigWidthMinus1
      }.

  Definition NF :=
    STRUCT_TYPE {
        "isNaN" :: Bool;
        "isInf" :: Bool;
        "isZero" :: Bool;
        "sign" :: Bool;
        "sExp" :: Bit (expWidth + 1);
        "sig" :: Bit sigWidthMinus1
      }.

  Definition ExceptionFlags :=
    STRUCT_TYPE {
        "invalid" :: Bool;
        "infinite" :: Bool;
        "overflow" :: Bool;
        "underflow" :: Bool;
        "inexact" :: Bool
      }.

  Definition OpOutput :=
    STRUCT_TYPE {
        "out" :: NF;
        "exceptionFlags" :: ExceptionFlags
      }.

  Section Ty.
    Open Scope kami_expr.

    Variable ty: Kind -> Type.

    Section FromFN.
      Variable fn: FN @# ty.
      
      Definition sign := fn @% "sign".
      Let expIn := fn @% "exp".
      Let fractIn := fn @% "frac".

      Definition infOrNaN := expIn == $$ (wones expWidth).
      Definition isZeroExpIn := expIn == $ 0.
      Definition isZeroFractIn := fractIn == $ 0.

      Definition isNaN := infOrNaN && ! isZeroFractIn.
      
      Definition normDist :=
        IF fractIn == $0
      then $sigWidthMinus2
      else countLeadingZeros (expWidth + 1) fractIn.

      Definition subnormFract := fractIn << (normDist + $ 1).

      Definition normalizedExp: Bit (expWidth + 1) @# ty :=
        (IF isZeroExpIn
         then $ 2 - $ (pow2 expWidthMinus1) - (normDist + $ 1)
         else ZeroExtend 1 expIn - $ (pow2 expWidthMinus1 - 1)).

      Definition normalizedFrac: Bit sigWidthMinus1 @# ty := IF isZeroExpIn then subnormFract else fractIn.
      Definition isZero := isZeroExpIn && isZeroFractIn.
      
      Definition getNF_from_FN: NF @# ty :=
        STRUCT {
            "isNaN" ::= isNaN;
            "isInf" ::= infOrNaN && isZeroFractIn;
            "isZero" ::= isZero;
            "sign" ::= sign;
            "sExp" ::= normalizedExp;
            "sig" ::= normalizedFrac
          }.
      
      Definition fracMsb := UniBit (TruncMsb _ 1) fractIn.
      Definition isSNaN := isNaN && fracMsb == $$ WO~0.

      
      Definition adjustedExp: Bit (expWidth + 1) @# ty :=
        (IF isZeroExpIn
         then ~ normDist
         else ZeroExtend 1 expIn) + ZeroExtend 1 ({<$$ WO~1, IF isZeroExpIn then $ 2 else $ 1 >}).

      Definition isSpecialMsb := UniBit (TruncMsb expWidth 1) adjustedExp == $ 1.
      Definition isSpecialLsb := ConstExtract expWidthMinus1 1 1 adjustedExp == $ 1.
      Definition isSpecial := isSpecialMsb && isSpecialLsb.
      
      Definition getRawFloat_from_FN: RawFloat @# ty :=
        STRUCT {
            "isNaN" ::= isSpecial && !isZeroFractIn;
            "isInf" ::= isSpecial && isZeroFractIn;
            "isZero" ::= isZero;
            "sign" ::= sign;
            "sExp" ::= adjustedExp;
            "sig" ::= IF isZeroExpIn then subnormFract else fractIn
          }.

    End FromFN.

    Section getRecFN_from_RawFloat.
      Variable rawFloat: RawFloat @# ty.
      Let sExp := rawFloat @% "sExp".

      Definition sExp_expWidth := UniBit (TruncMsb _ 1) sExp.
      Definition sExp_expWidthMinus1 := UniBit (TruncMsb _ 1)
                                               (UniBit (TruncLsb _ 1) sExp).
      Definition sExp_expWidthMinus2 := UniBit (TruncMsb _ 1)
                                               (UniBit (TruncLsb _ 1)
                                                       (UniBit (TruncLsb _ 1) sExp)).

      Definition getRecFN_from_RawFloat: RecFN @# ty :=
        STRUCT {
            "sign" ::= rawFloat @% "sign";
            "isZeroNaNInf0" ::= (IF rawFloat @% "isZero" then $$ WO~0 else
                                   sExp_expWidth);
            "isZeroNaNInf1" ::= (IF rawFloat @% "isZero" then $$ WO~0 else
                                   sExp_expWidthMinus1);
            "isZeroNaNInf2" ::= ((IF rawFloat @% "isZero" then $$ WO~0 else
                                    sExp_expWidthMinus2) | (IF rawFloat @% "isNaN" then
                                                              $$ WO~1 else $$ WO~0));
            "exp" ::= UniBit (TruncLsb _ 1)
                             (UniBit (TruncLsb _ 1)
                                     (UniBit (TruncLsb _ 1) sExp));
            "fract" ::= rawFloat @% "sig"
          }.

    End getRecFN_from_RawFloat.

    Section getRawFloat_from_RecFN.
      Variable recFN: RecFN @# ty.

      Let exp := recFN @% "exp".

      Definition isZeroNaNInf0 := recFN @% "isZeroNaNInf0".
      Definition isZeroNaNInf1 := recFN @% "isZeroNaNInf1".
      Definition isZeroNaNInf2 := recFN @% "isZeroNaNInf2".

      Definition isZeroRecFN := isZeroNaNInf0 == $0 && isZeroNaNInf1 == $0 && isZeroNaNInf2 == $0.
      Definition isNaN_or_Inf := isZeroNaNInf0 == $1 && isZeroNaNInf1 == $1.

      Definition get_exp_from_RecFN: Bit (expWidth + 1) @# ty :=
        {< isZeroNaNInf0, isZeroNaNInf1, isZeroNaNInf2, exp >}.
      
      Definition getRawFloat_from_RecFN: RawFloat @# ty :=
        STRUCT {
            "isNaN" ::= isNaN_or_Inf && isZeroNaNInf2 == $ 1;
            "isInf" ::= isNaN_or_Inf && isZeroNaNInf2 == $ 0;
            "isZero" ::= isZeroRecFN;
            "sign" ::= recFN @% "sign";
            "sExp" ::= get_exp_from_RecFN;
            "sig" ::= recFN @% "fract"
            }.

    End getRawFloat_from_RecFN.

    Section getFN_from_NF.
      Variable nf: NF @# ty.

      Let exp := nf @% "sExp".
      Let frac := nf @% "sig".
      Let isZeroNF := nf @% "isZero".
      Let isNaNNF := nf @% "isNaN".
      Let isInfNF := nf @% "isInf".

      Definition isSubnormalExp := exp <s ($ 2 - $(pow2 expWidthMinus1)).
      Definition subnormDist := $1 - $(pow2 expWidthMinus1) - exp.
      Definition truncFrac : Expr ty (SyntaxKind (Bit (sigWidthMinus2))).
        refine (UniBit (TruncMsb 1 sigWidthMinus2)
                       (castBits _ frac)).
        rewrite Nat.add_comm; reflexivity.
      Defined.
      Definition subnormFrac := {< $$(WO~1), truncFrac >} >> subnormDist.

      Definition nonSpecializedFrac := IF isSubnormalExp then subnormFrac else frac.
      Definition nonSpecializedExp: Bit expWidth @# ty :=
        IF isSubnormalExp
      then $0
      else UniBit (TruncLsb _ 1) (exp + $(pow2 expWidthMinus1 - 1)).

      Definition specializedExp :=
        (IF isZeroNF
         then $0
         else IF (isNaNNF || isInfNF)
         then $$(wones expWidth)
         else nonSpecializedExp).
      
      Definition specializedFrac :=
        (IF (isZeroNF || isInfNF)
         then $0
         else (IF isNaNNF
               then (IF frac == $0
                     then {< $$ WO~1, $ 0 >}
                     else frac) (* {< $$ WO~1, $ 0 >} *)
               else nonSpecializedFrac)).
 
      Definition getFN_from_NF: FN @# ty :=
        STRUCT {
            "sign" ::= nf @% "sign" (* && !(nf @% "isNaN") *);
            "exp" ::= specializedExp;
            "frac" ::= specializedFrac
          }.
                       
    End getFN_from_NF.
    
    
    Section getRawFloat_from_NF.
      Variable nf: NF @# ty.

      Definition getRawFloat_from_NF: RawFloat @# ty :=
        STRUCT {
            "isNaN" ::= (nf @% "isNaN");
            "isInf" ::= (nf @% "isInf");
            "isZero" ::= (nf @% "isZero");
            "sign" ::= (nf @% "sign");
            "sExp" ::= (nf @% "sExp" - $(pow2 expWidth));
            "sig" ::= (nf @% "sig")
          }.

    End getRawFloat_from_NF.
    
    Section getNF_from_RawFloat.
      Variable rf: RawFloat @# ty.

      Definition getNF_from_RawFloat: NF @# ty :=
        STRUCT {
            "isNaN" ::= (rf @% "isNaN");
            "isInf" ::= (rf @% "isInf");
            "isZero" ::= (rf @% "isZero");
            "sign" ::= (rf @% "sign");
            "sExp" ::= (rf @% "sExp" + $(pow2 expWidth));
            "sig" ::= (rf @% "sig")
          }.

    End getNF_from_RawFloat.

    Definition getRecFN_from_FN fn := getRecFN_from_RawFloat (getRawFloat_from_FN fn).
    Definition getFN_from_RawFloat rf := getFN_from_NF (getNF_from_RawFloat rf).

    Definition getNF_from_RecFN rfn := getNF_from_RawFloat (getRawFloat_from_RecFN rfn).

    Definition getFN_from_RecFN rfn := getFN_from_NF (getNF_from_RecFN rfn).

    Definition getRecFN_from_NF nf := getRecFN_from_FN (getFN_from_NF nf).

 End Ty.

End Definitions.

Notation round_near_even   := (natToWord 3 0).
Notation round_minMag      := (natToWord 3 1).
Notation round_min         := (natToWord 3 2).
Notation round_max         := (natToWord 3 3).
Notation round_near_maxMag := (natToWord 3 4).
Notation round_odd         := (natToWord 3 6).
