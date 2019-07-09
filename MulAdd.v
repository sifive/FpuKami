Require Import Kami.All Definitions Round.
Require Import Arith.Compare_dec.

Section Definitions.
  Variable expWidthMinus2 sigWidthMinus2: nat.
  
  Local Notation expWidthMinus1 := (expWidthMinus2 + 1).
  Local Notation expWidth := (expWidthMinus1 + 1).

  Local Notation sigWidthMinus1 := (sigWidthMinus2 + 1).
  Local Notation sigWidth := (sigWidthMinus1 + 1).

  Section Ty.
    Variable ty: Kind -> Type.

    Definition MulAdd_Input :=
      STRUCT_TYPE {
          "op" :: Bit 2 ;
          "a" :: NF expWidthMinus2 sigWidthMinus2 ;
          "b" :: NF expWidthMinus2 sigWidthMinus2 ;
          "c" :: NF expWidthMinus2 sigWidthMinus2 ;
          "roundingMode" :: Bit 3 ;
          "detectTininess" :: Bool
        }.

    Definition MulAdd_Output :=
      STRUCT_TYPE {
          "out" :: NF expWidthMinus2 sigWidthMinus2;
          "exceptionFlags" :: ExceptionFlags
        }.

    Section MulAdd.
      Variable input: MulAdd_Input @# ty.
      Open Scope kami_expr.

      Definition inA := input @% "a".
      Definition inB := input @% "b".
      Definition inC := input @% "c".
      Definition op  := input @% "op".

      Definition extendSig (x: Expr ty (SyntaxKind (Bit sigWidthMinus1)))
                            : Expr ty (SyntaxKind (Bit (2*sigWidthMinus1 + 1 + 1))).
      Proof.
        refine (castBits _ (ZeroExtend sigWidth ({< Const ty WO~1, x >}))).
        abstract lia.
      Defined.

      Open Scope kami_action.

      Definition MulAdd_expr
        :  OpOutput expWidthMinus2 sigWidthMinus2 ## ty.
        Proof.
          refine (
            LETC isNaNA <- inA @% "isNaN";
            LETC isNaNB <- inB @% "isNaN";
            LETC isNaNC <- inC @% "isNaN";
            LETC inNaN <- #isNaNA || #isNaNB || #isNaNC;

            LETC inInf <- (inA @% "isInf") || (inB @% "isInf") || (inC @% "isInf");
            LETC inInfOrNaN <- #inNaN || #inInf;
            LETC inAOrBZero <- inA @% "isZero" || inB @% "isZero";

            LETC isSignalingNaNA <- (UniBit (TruncMsb _ 1 ) (inA @% "sig")) == $0;
            LETC isSignalingNaNB <- (UniBit (TruncMsb _ 1 ) (inB @% "sig")) == $0;
            LETC isSignalingNaNC <- (UniBit (TruncMsb _ 1 ) (inC @% "sig")) == $0;

            LETC inputSignalingNaN <- 
                 ((#isSignalingNaNA && #isNaNA)
                 || (#isSignalingNaNB && #isNaNB)
                 || (#isSignalingNaNC && #isNaNC));

            LETC opCNeg <- ((op == $1) || (op == $3));
            LETC CNeg <- (IF inC @% "sign"
                         then !#opCNeg
                         else #opCNeg);
            
            LETC opANeg <- UniBit (TruncMsb 1 1) op == $1;
            
            LETC rawMultSign <- (inA @% "sign") ^^ (inB @% "sign");
                               
            LETC multSign <- (IF #opANeg then !#rawMultSign else #rawMultSign);

            LETC extendInASig <- extendSig (inA @% "sig");
            
            LETC extendInBSig <- extendSig (inB @% "sig");

            LETC mulABSig: Bit (2 * sigWidthMinus1 + 1 + 1) <- #extendInASig * #extendInBSig;

            LETC mulABSig_good <-
                ({< Const ty (natToWord 1 0), #mulABSig >} <=
                 (castBits _ ({<Const ty WO~1, Const ty (natToWord (2*sigWidth) 0)>}) -
                  castBits _ (ZeroExtend sigWidthMinus1 ({<Const ty WO~1, Const ty (natToWord (sigWidth + 1) 0)>})) +
                  castBits _ (Const ty (natToWord (2*sigWidth + 1) 1)))) &&
                (#mulABSig >= castBits _ (ZeroExtend 1 ({<Const ty WO~1, Const ty (natToWord (2 * sigWidthMinus1) 0) >})));

            LETC mulABSigNormDist <- countLeadingZeros (expWidth + 1 + 1) #mulABSig;
            
            LETC expC <- (IF inC @% "isZero"
                         then $2 - $(pow2 expWidthMinus1) - $sigWidth
                         else inC @% "sExp");

            LETC normalizedMulABSig: Bit (2 * sigWidthMinus1 + 1 + 1) <-
                                        (IF #inAOrBZero
                                         then $0
                                         else #mulABSig << #mulABSigNormDist);

            LETC sumABExp <- (IF #inAOrBZero
                             then $2 - $(pow2 expWidthMinus1) - $sigWidth
                             else ((SignExtend 1 (inA @% "sExp")) +
                                   (SignExtend 1 (inB @% "sExp")) +
                                   ($1 - #mulABSigNormDist)));

            LETC extendedInCSig : Bit (2*sigWidthMinus1 + 1 + 1) <-
                                     (IF inC @% "isZero"
                                      then $0
                                      else castBits _ ({< Const ty WO~1, inC @% "sig", $$(wzero sigWidth)>}));

            LETC extendedCExp <- SignExtend 1 #expC;

            LETC sumAbExp_lt_extendedCExp <- #sumABExp <s #extendedCExp;
            
            LETC biggestExp <-
                (IF #sumAbExp_lt_extendedCExp
                 then #extendedCExp
                 else #sumABExp);

            LETC sigDist <-
                (IF #sumAbExp_lt_extendedCExp
                 then #extendedCExp - #sumABExp
                 else #sumABExp - #extendedCExp);

            LETC tailDist <-
                (IF $(2*sigWidthMinus1 + 1 + 1) > #sigDist
                 then $(2*sigWidthMinus1 + 1 + 1) - #sigDist
                 else $0);

            LETC tailSig <-
                (IF #sumAbExp_lt_extendedCExp
                 then #normalizedMulABSig << #tailDist
                 else #extendedInCSig << #tailDist);

            LETC treatedSumMulABSig <-
                (IF #sumAbExp_lt_extendedCExp
                 then ZeroExtend 1 (#normalizedMulABSig >> #sigDist)
                 else  ZeroExtend 1 #normalizedMulABSig);

            LETC roundedSumMulABSig: Bit (2*sigWidthMinus1 + 1 + 1 + 1 + 1) <-
                castBits _ (IF #sumAbExp_lt_extendedCExp && (#tailSig != $0)
                 then {< #treatedSumMulABSig, $$ WO~1 >}
                 else {< #treatedSumMulABSig, $$ WO~0 >});

            LETC treatedCSig <-
                (IF !#sumAbExp_lt_extendedCExp
                 then ZeroExtend 1 (#extendedInCSig >> #sigDist)
                 else ZeroExtend 1 #extendedInCSig);

            LETC roundedCSig : Bit (2*sigWidthMinus1 + 1 + 1 + 1 + 1) <-
                castBits _ (IF !#sumAbExp_lt_extendedCExp && (#tailSig != $0 )
                 then {< #treatedCSig, $$ WO~1 >}
                 else {< #treatedCSig, $$ WO~0 >});


            LETC treatedSubs <- (IF #roundedSumMulABSig < #roundedCSig
                                then #roundedCSig - #roundedSumMulABSig
                                else #roundedSumMulABSig - #roundedCSig);

            LETC treatedSign <- (IF (#CNeg == #multSign)
                                then #multSign
                                else (IF ((!#inInf && !(#inAOrBZero && inC @% "isZero")
                                             && (#roundedSumMulABSig < #roundedCSig)) || (inC @% "isInf"))
                                      then #CNeg
                                      else #multSign));
         
            LETC sumSigs <-
                (IF #CNeg == #multSign
                 then #roundedSumMulABSig + #roundedCSig
                 else #treatedSubs);

            LETC sumSigsNormDist <- (countLeadingZeros (expWidth+1+1) #sumSigs);

            LETC normalizedSumSigs <-
                #sumSigs << #sumSigsNormDist;


            LETC treatedBiggestExp <- #biggestExp + ($1 - #sumSigsNormDist);
            LETC resultsZero <- #sumSigs == $0;

            LETC muladd_invalid <-
                ((inA @% "isInf" && inB @% "isZero")
                 || (inA @% "isZero" && inB @% "isInf")
                 || ((inA @% "isInf" || inB @% "isInf") && inC @% "isInf"
                      && (#CNeg != #multSign) && !#inNaN)
                 || #inputSignalingNaN);
            LETC outNaN <- (#inNaN || #muladd_invalid);

            LETC infinitePrecisionMulAdd
            : NF expWidthMinus1 (2*sigWidthMinus1 + 1 + 1) <-
                 STRUCT {
                   "isNaN" ::= #outNaN;
                   "isInf" ::= !#outNaN && #inInf;
                   "isZero" ::= !#outNaN && !#inInf && (#resultsZero || (#inAOrBZero) && (inC @% "isZero"));
                   "sign" ::= #treatedSign;
                   "sExp" ::= #treatedBiggestExp;
                   "sig" ::= ignoreMsb (castBits _ #normalizedSumSigs)
                 };
            
            LETC muladdRoundInput: RoundInput _ _ <-
                                             STRUCT {
                                               "in" ::= #infinitePrecisionMulAdd;
                                               "afterRounding" ::= input @% "detectTininess";
                                               "roundingMode" ::= input @% "roundingMode"
                                             };

            LETE muladdRound : OpOutput expWidthMinus2 sigWidthMinus2 <-
                                        (RoundNF_expr expWidthMinus2 sigWidthMinus2
                                                        (pow2 (expWidthMinus2 + 1) - 2)%nat
                                                        (pow2 (expWidthMinus2 + 1) + (sigWidthMinus2 + 1) - 2)%nat
                                                        (pow2 (expWidthMinus2 + 1) - 1)%nat
                                                        #muladdRoundInput);
            LETC muladdRound_out: NF expWidthMinus2 sigWidthMinus2 <- #muladdRound @% "out";

            LETC muladdRound_flags: ExceptionFlags <- #muladdRound @% "exceptionFlags";
            LETC muladdInexact <-
                (!(#muladdRound_out @% "isNaN") && (#tailSig != $0));

            LETC infOrInvalid <- (#muladd_invalid || #inInfOrNaN );

            LETC muladd_exceptionFlags
            : ExceptionFlags <- STRUCT {
                               "invalid" ::= #muladd_invalid;
                               "infinite" ::= $$ false;
                               "overflow" ::= !#infOrInvalid && (#muladdRound_flags @% "overflow");
                               "underflow" ::= !#infOrInvalid && (#muladdRound_flags @% "underflow");
                               "inexact" ::= !#infOrInvalid && (#muladdRound_flags @% "inexact" || #muladdInexact)
                             };

            LETC muladdRound_out_final : NF expWidthMinus2 sigWidthMinus2 <-
                #muladdRound_out @%["sign" <- 
                    (IF (!(#muladd_exceptionFlags @% "inexact")
                            && (#muladdRound_out @% "isZero")
                            && (((#multSign == inC @% "sign" && #opCNeg)
                                 || (#multSign != inC @% "sign" && !#opCNeg))))
                           then (IF (((input @% "roundingMode") == $$ round_min)
                                  && (!(#opCNeg && inC @% "sign" && !(#muladdRound_out @% "sign"))))
                                 then $$ true
                                 else $$ false)
                     else #muladdRound_out @% "sign")];

            LETC MulAdd: OpOutput expWidthMinus2 sigWidthMinus2 <-
                                 STRUCT {
                                   "out" ::= #muladdRound_out_final;
                                   "exceptionFlags" ::= #muladd_exceptionFlags
                                 };
            RetE #MulAdd); abstract lia.
        Defined.

      Definition MulAdd_action: ActionT ty (OpOutput expWidthMinus2 sigWidthMinus2)
        := convertLetExprSyntax_ActionT MulAdd_expr.

      Close Scope kami_action.

    End MulAdd.
  End Ty.

End Definitions.
