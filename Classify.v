Require Import Kami.Syntax Definitions.

Section Definitions.
  Variable expWidthMinus2 sigWidthMinus2: nat.
  
  Local Notation expWidthMinus1 := (expWidthMinus2 + 1).
  Local Notation expWidth := (expWidthMinus1 + 1).

  Local Notation sigWidthMinus1 := (sigWidthMinus2 + 1).
  Local Notation sigWidth := (sigWidthMinus1 + 1).

  Local Notation FN := (FN expWidthMinus2 sigWidthMinus2).
  Local Notation RawFloat := (RawFloat expWidthMinus2 sigWidthMinus2).
  Local Notation RecFN := (RecFN expWidthMinus2 sigWidthMinus2).

  Section Ty.
    Variable ty: Kind -> Type.

    Variable fn: FN @# ty.


    Section classify.
      Variable lenMinus10: nat.

      Definition classify_spec: Bit (10 + lenMinus10) @# ty :=
        ZeroExtend _
                   ({<
                     pack (isNaN fn && !isSNaN fn),
                     pack (isSNaN fn),
                     pack (!sign fn && infOrNaN fn && isZeroFractIn fn),
                     pack (!sign fn && !infOrNaN fn && !isZeroExpIn fn),
                     pack (!sign fn && isZeroExpIn fn && !isZeroFractIn fn),
                     pack (!sign fn && isZeroExpIn fn && isZeroFractIn fn),
                     pack (sign fn && isZeroExpIn fn && isZeroFractIn fn),
                     pack (sign fn && isZeroExpIn fn && !isZeroFractIn fn),
                     pack (sign fn && !infOrNaN fn && !isZeroExpIn fn),
                     pack (sign fn && infOrNaN fn && isZeroFractIn fn)
                     >})%kami_expr.
      
      Section RawFloat.
        Variable rawFloat: RawFloat @# ty.

        Let minNormExp := pow2 expWidthMinus1 + 2.

        Open Scope kami_expr.

        Definition isFiniteNonzero := ! (rawFloat @% "isNaN") && ! (rawFloat @% "isInf") && ! (rawFloat @% "isZero").

        Definition isSubnormal := (rawFloat @% "sExp") < {< $$ WO~0, $$ WO~1, $ 2 >}.

        Definition isSigNaNRawFloat_frac :=
          UniBit (TruncMsb sigWidthMinus2 1) (rawFloat @% "sig") == $ 0.

        Definition isSigNaNRawFloat :=
          rawFloat @% "isNaN" && isSigNaNRawFloat_frac.

        Definition classifyRawFloat: Bit (10 + lenMinus10) @# ty :=
          ZeroExtend _ ({<
                         pack ((rawFloat @% "isNaN") && ! isSigNaNRawFloat ),
                         pack isSigNaNRawFloat,
                         pack (! (rawFloat @% "sign") && (rawFloat @% "isInf")),
                         pack (! (rawFloat @% "sign") && isFiniteNonzero && ! isSubnormal),
                         pack (! (rawFloat @% "sign") && isFiniteNonzero &&   isSubnormal),
                         pack (! (rawFloat @% "sign") && (rawFloat @% "isZero")),
                         pack (  (rawFloat @% "sign") && (rawFloat @% "isZero")),
                         pack (  (rawFloat @% "sign") && isFiniteNonzero &&   isSubnormal),
                         pack (  (rawFloat @% "sign") && isFiniteNonzero && ! isSubnormal),
                         pack (  (rawFloat @% "sign") && (rawFloat @% "isInf")) >}).
      End RawFloat.

      Section RecFN.
        Variable recFN: RecFN @# ty.

        Definition classifyRecFN: Bit (10 + lenMinus10) @# ty :=
          classifyRawFloat (getRawFloat_from_RecFN recFN).
      End RecFN.

      Definition classify_impl: Bit (10 + lenMinus10) @# ty :=
        classifyRecFN (getRecFN_from_FN fn).

    End classify.
  End Ty.
End Definitions.
