Require Import Kami.Syntax Definitions.

Section Definitions.
  Variable expWidthMinus2 sigWidthMinus2: nat.
  
  Local Notation expWidthMinus1 := (expWidthMinus2 + 1).
  Local Notation expWidth := (expWidthMinus1 + 1).

  Local Notation sigWidthMinus1 := (sigWidthMinus2 + 1).
  Local Notation sigWidth := (sigWidthMinus1 + 1).

  Section Ty.
    Variable ty: Kind -> Type.

    Definition Compare_Output :=
      STRUCT {
          "gt" :: Bool;
          "eq" :: Bool;
          "lt" :: Bool;
          "exceptionFlags" :: ExceptionFlags
        }.

    Section Compare.
      Variable a: NF expWidthMinus2 sigWidthMinus2 @# ty.
      Variable b: NF expWidthMinus2 sigWidthMinus2 @# ty.
      Open Scope kami_expr.

      Definition signA := a @% "sign".
      Definition expA  := a @% "sExp".
      Definition sigA := a @% "sig".

      Definition signB := b @% "sign".
      Definition expB  := b @% "sExp".
      Definition sigB := b @% "sig".

      Open Scope kami_action.
      Definition Compare_expr
        :  Compare_Output ## ty
        := LETC invalid <- a @% "isNaN" || b @% "isNaN";
           LETC bothInfs <- a @% "isInf" && b @% "isInf";
           LETC bothZeros <- a @% "isZero" && b @% "isZero";
           LETC eitherZero <- a@% "isZero" || b @% "isZero";

           LETC eqExp <- expA == expB;
           LETC eqSign <- signA == signB;
           LETC eqSig <- sigA == sigB;

           LETC eqMags <- #eqExp && #eqSig;

           LETC ltMags_common <- (b@%"isInf") || ((!(a@%"isInf")) && ((expA <s expB) || (#eqExp && (sigA < sigB))));

           LETC ltMags <- (signA && !signB)
           || (!signA && !signB && #ltMags_common)
           || (signA && signB && !#ltMags_common && !#eqMags);

           LETC zLtPos <- a @% "isZero" && !signB;
           LETC aLtInf <- !(a @% "isInf") && !signB && (b @% "isInf");
           LETC ltSign <- signA && !signB;
           LETC negLtZero <- (signA && b @% "isZero");

           LETC eq <- #bothZeros || (!#eitherZero && #eqSign && (#bothInfs || #eqMags));
           LETC lt <-
               !#bothZeros
               && (#ltSign
                   || (!#bothInfs && (#zLtPos || #aLtInf || #negLtZero || #ltMags)));

           LETC gt <- !#lt && !#eq;

           LETC flags: ExceptionFlags <- STRUCT {
                                       "invalid" ::= #invalid;
                                       "infinite" ::= $$false;
                                       "overflow" ::= $$false;
                                       "underflow" ::= $$false;
                                       "inexact" ::= $$false
                                     };
           LETC Compare: Compare_Output <- STRUCT {
                                                "gt" ::= !#invalid && #gt;
                                                "eq" ::= !#invalid && #eq;
                                                "lt" ::= !#invalid && #lt;
                                                "exceptionFlags" ::= #flags
                                              };
           RetE #Compare.

      Definition Compare_action
        :  ActionT ty (Compare_Output)
        := convertLetExprSyntax_ActionT Compare_expr.

    End Compare.
  End Ty.
End Definitions.
