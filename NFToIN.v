Require Import Kami.Syntax Definitions FpuKami.FpuProperties.
  
Section Definitions.
  Open Scope nat.
  Variable intWidthMinus2 expWidthMinus2 sigWidthMinus2: nat.
  Local Notation intWidthMinus1  := (intWidthMinus2 + 1).
  Local Notation intWidth := (intWidthMinus1 + 1).
  Local Notation expWidthMinus1 := (expWidthMinus2 + 1).
  Local Notation expWidth := (expWidthMinus1 + 1).
  Local Notation sigWidthMinus1 := (sigWidthMinus2 + 1).
  Local Notation sigWidth := (sigWidthMinus1 + 1).
  Variable expWidth_prop: expWidthMinus2 >= 2.
  Variable expWidthMinus2_plus4_gt_sigWidth: pow2 expWidthMinus2 + 4 > sigWidth.
  
  Section Ty.
    Variable ty: Kind -> Type.
    Section Convert.

      Definition NFToINInput := STRUCT_TYPE {
                                "inNF" :: NF expWidthMinus2 sigWidthMinus2;
                                "roundingMode" :: Bit 3;
                                "signedOut" :: Bool
                              }.

      Definition NFToINOutput := STRUCT_TYPE {
                                     "outIN" :: Bit intWidth;
                                     "flags" :: ExceptionFlags
                                   }.

      Open Scope kami_expr.
      Variable input: NFToINInput  @# ty.


      Definition roundingMode_near_even := input @% "roundingMode" == $$ round_near_even.
      Definition roundingMode_minMag := input @% "roundingMode" == $$ round_minMag.
      Definition roundingMode_min := input @% "roundingMode" == $$ round_min.
      Definition roundingMode_max := input @% "roundingMode" == $$ round_max.
      Definition roundingMode_odd := input @% "roundingMode" == $$ round_odd.
      Definition roundingMode_near_maxMag := input @% "roundingMode" == $$ round_near_maxMag.
      
      Definition signedOut := input @% "signedOut" .
      Definition inNF  := input @% "inNF".
      Definition inExp := inNF @% "sExp".
      Definition inSig := inNF @% "sig".
      Definition inSign := inNF @% "sign".

      Definition bigIntSz: nat :=(pow2 expWidthMinus1).
      
      Definition ZeroExpand n sz `(i: Expr ty (SyntaxKind (Bit n)))
        :Expr ty (SyntaxKind (Bit (n + sz))).
      Proof.
        refine (castBits _ ({< i, $$(wzero sz) >})); abstract intuition.
      Defined.

      Open Scope kami_action.

      Definition NFToIN_expr
      :  NFToINOutput ## ty.
      Proof.
        refine (
          LETC isExpPositive <- (inExp >=s $0);

          LETC leadingOneSig: Bit sigWidth <- {< $$ WO~1, inSig >};
          LETC bigSig: Bit bigIntSz <- castBits _ (ZeroExpand (bigIntSz - sigWidth) #leadingOneSig);
          LETC tailSig: Bit sigWidth <- (IF #isExpPositive || inNF @% "isZero"
                                        then #leadingOneSig << (inExp+$1)
                                        else (IF inExp == ($0 - $1)
                                              then #leadingOneSig
                                              else #leadingOneSig >> $$WO~1));

          LETC isTailMiddle : Bool <- (#tailSig == {< $$WO~1, $$ (wzero sigWidthMinus1)>});
          LETC isTailGtMiddle : Bool <- (#tailSig > {< $$WO~1, $$ (wzero sigWidthMinus1)>});

          LETC correctSig: Bit bigIntSz <- #bigSig >> ($bigIntSz - inExp - $1);

          LETC truncSig <- match Compare_dec.lt_dec intWidth bigIntSz with
                          | left _ => UniBit (TruncLsb (intWidth) (bigIntSz - intWidth)) (castBits _ #correctSig)
                          | _ => castBits _ (ZeroExtend (intWidth - bigIntSz) #correctSig)
                          end;
 
          LETC truncSigHead <- match Compare_dec.lt_dec intWidth bigIntSz with
                          | left _ => UniBit (TruncMsb (intWidth) (bigIntSz - intWidth)) (castBits _ #correctSig)
                          | _ => $ 0
                          end;

          LETC isTruncSigOdd: Bool <- UniBit (TruncLsb 1 intWidthMinus1) (castBits _ #truncSig) == $1 ;
          LETC roundIncr <-
              ((roundingMode_min && inSign && #tailSig != $0)
               || (roundingMode_max && !inSign && #tailSig != $0)
               || (roundingMode_near_even && ((#isTailMiddle && #isTruncSigOdd)
                                                ||#isTailGtMiddle))
               || (roundingMode_near_maxMag && (#isTailMiddle || #isTailGtMiddle)));

          LETC roundIN : Bit intWidth <- (IF #roundIncr then #truncSig + $1 else #truncSig);
          LETC roundOrJammIN: (Bit intWidth) <-
                                                (IF (roundingMode_odd && #tailSig != $0)
                                                 then castBits _ ({< UniBit (TruncMsb 1 intWidthMinus1) (castBits _ #roundIN), Const ty WO~1 >})
                                                 else #roundIN);
          LETC signedIN <-
              IF inSign
          then $0 - #roundOrJammIN
          else #roundOrJammIN;

          LETC overflowBiasOut: Bit (expWidth + 1) <-
                                ZeroExtend _ (IF signedOut
                                              then $1
                                              else $0);


          LETC overflowBiasSign: Bit (expWidth + 1) <-
                                ZeroExtend _ (IF inSign
                                              then $1
                                              else $0);

          LETC overflow_afterRound <- !inSign
                                       && (((#signedIN <s $0) && signedOut)
                                           || (!signedOut
                                                && #roundIncr
                                                && (#truncSig == $$(wones intWidth))));

          LETC overflow_exp <- ((inExp >s $intWidthMinus1 - #overflowBiasOut)
                           && !(inSign
                                 && (#signedIN == {<$$WO~1, $$(wzero intWidthMinus1)>})
                                 && inExp == $intWidthMinus1));

          LETC roundsToZero <- (#signedIN == $0) && (inExp <=s $0);

          LETC invalidExec <-
              (inNF @% "isNaN"
               || inNF @% "isInf"
               || #overflow_exp
               || #overflow_afterRound
               || (inSign && !signedOut && !#roundsToZero));

          LETC finalIN <-
              (IF !#invalidExec
               then #signedIN
               else (IF signedOut
                     then (IF inSign && !(inNF @% "isNaN")
                           then {<$$ WO~1, $$(wzero intWidthMinus1)>}
                           else {<$$ WO~0, $$(wones intWidthMinus1)>})
                     else (IF inSign && !(inNF @% "isNaN")
                           then $0
                           else $$(wones intWidth))));

          LETC outFlags: ExceptionFlags <- STRUCT {
                                         "invalid" ::= (#invalidExec);
                                         "infinite" ::= $$false;
                                         "overflow" ::= $$false;
                                         "underflow" ::= $$false;
                                         "inexact" ::= !#invalidExec && (#tailSig != $0)
                                       };

          LETC output: NFToINOutput <- STRUCT {
                                     "outIN" ::= #finalIN;
                                     "flags" ::= #outFlags
                                   };
          RetE #output);
          abstract (unfold bigIntSz in *; pose proof (expWidth_ge_sigWidth _ expWidth_prop expWidthMinus2_plus4_gt_sigWidth); simpl; lia).
      Defined.
      
      Definition NFToIN_action: ActionT ty (NFToINOutput)
        := convertLetExprSyntax_ActionT NFToIN_expr.

    End Convert.

  End Ty.
End Definitions.
