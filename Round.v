Require Import Kami.AllNotations.
Require Import FpuKami.Definitions.

Definition Pair (A B: Kind) := (STRUCT_TYPE {
                                    "fst" :: A;
                                    "snd" :: B
                               }).

Section RoundAny.
   Variable ty: Kind -> Type.
   Variable inExpWidthMinus2 inSigWidthMinus2: nat.

   Local Notation inExpWidthMinus1 := (inExpWidthMinus2 + 1).
   Local Notation inExpWidth := (inExpWidthMinus1 + 1).

   Local Notation inSigWidthMinus1 := (inSigWidthMinus2 + 1).
   Local Notation inSigWidth := (inSigWidthMinus1 + 1).

   Variable outExpWidthMinus2 outSigWidthMinus2: nat. 
   Local Notation outExpWidthMinus1 := (outExpWidthMinus2 + 1).
   Local Notation outExpWidth := (outExpWidthMinus1 + 1).

   Local Notation outSigWidthMinus1 := (outSigWidthMinus2 + 1).
   Local Notation outSigWidth := (outSigWidthMinus1 + 1).

   Definition RoundInput := STRUCT_TYPE {
                                "in" :: NF inExpWidthMinus2 inSigWidthMinus2;
                                "afterRounding" :: Bool;
                                "roundingMode" :: Bit 3
                              }.

   Variable underflowInExpSltMinus underflowToZeroInExpSltMinus overflowExpGlt: nat.
   
   Open Scope kami_expr.

   Variable input : RoundInput @# ty.

   Definition ignoreMsb {n:nat} (x: Expr ty (SyntaxKind (Bit (n+1)))) :=
     UniBit (TruncLsb n 1) x.

   Open Scope kami_action.

   Definition RoundNF_expr: LetExprSyntax ty (OpOutput outExpWidthMinus2 outSigWidthMinus2).
     refine (
         LETE roundingMode_near_even <- RetE (input @% "roundingMode" == $$ round_near_even);
         LETE roundingMode_minMag <- RetE (input @% "roundingMode" == $$ round_minMag);
         LETE roundingMode_min <- RetE (input @% "roundingMode" == $$ round_min);
         LETE roundingMode_max <- RetE (input @% "roundingMode" == $$ round_max);
         LETE roundingMode_odd <- RetE (input @% "roundingMode" == $$ round_odd);
         LETE roundingMode_near_maxMag <- RetE (input @% "roundingMode" == $$ round_near_maxMag);
         LETE nfIn   <- RetE (input @% "in");
         LETE inSign <- RetE (#nfIn @% "sign");
         LETE inSig  <- RetE (#nfIn @% "sig");
         LETE inExp : Bit (inExpWidth + 1) <- RetE (#nfIn @% "sExp");


         LETE subnormal <- RetE match Compare_dec.lt_dec outSigWidthMinus2 inSigWidthMinus2 with
                                | left _ => (#inExp <s (* $2 - $(pow2 outExpWidthMinus1) *) $0 - $underflowInExpSltMinus)
                                | _ => $$false
                                end;

         LETE subNormDist <- RetE (IF #subnormal
                                   then ($2 - $(2 ^ outExpWidthMinus1) - #inExp)
                                   else $0);
         
         LETE leadingOneSig: Bit inSigWidth <-
                                RetE ({<$$WO~1, #inSig>});

         LETE signedSubnormShift <- RetE (IF $outSigWidth <s #subNormDist
                                          then $0
                                          else $outSigWidthMinus1 - #subNormDist);
         
         LETE tailSig: Bit inSigWidth <- RetE (IF $outSigWidth <s #subNormDist
                                               then (#leadingOneSig >> $$(WO~1))
                                               else (#leadingOneSig << ($outSigWidthMinus1 - #subNormDist + $1)));
         
         LETE underflowsToZero <- RetE (#inExp <s (* $2 - $(pow2 outExpWidthMinus1) - $outSigWidthMinus1 *) $0 - $ underflowToZeroInExpSltMinus);

         LETE isTailMiddle : Bool <-
                                 RetE (#tailSig == {< $$WO~1, $$ (wzero inSigWidthMinus1)>});
         
         LETE isTailGtMiddle : Bool <-
                                   RetE (#tailSig > {< $$WO~1, $$ (wzero inSigWidthMinus1)>});
         
         LETE overflow <- RetE match Compare_dec.le_dec outExpWidthMinus2 inExpWidthMinus2 with
                               | left _ => (#inExp >s (* $(pow2 outExpWidthMinus1) - $1 *) $ overflowExpGlt)
                               | _ => $$false
                               end;

         LETE roundToInf: Bool <-
                              RetE (#roundingMode_near_even
                                    || #roundingMode_near_maxMag
                                    || (#roundingMode_min && #inSign)
                                    || (#roundingMode_max && !#inSign));
         

         LETE inexact_underflow: Bool <-
                                    RetE (!(#nfIn @% "isZero")
                                           && !(#nfIn @% "isNaN")
                                           && !(#nfIn @% "isInf")
                                           && (#tailSig != $0
                                               || #underflowsToZero));
         
         LETE inexact <-
             RetE match Compare_dec.lt_dec outExpWidthMinus2 inExpWidthMinus2,
                        Compare_dec.lt_dec outSigWidthMinus2 inSigWidthMinus2
                  with
                  | right _, right _ => $$ false
                  | _, _ => (!(#nfIn @% "isInf") && !(#nfIn @% "isNaN")) && (#overflow || #inexact_underflow)
                  end;



         LETE expSigPlus1RoundSig : Pair (Pair Bool Bool) (Bit outSigWidthMinus1) <- 
                                         match Compare_dec.lt_dec outSigWidthMinus2 inSigWidthMinus2 with
                                         | left isLt =>
                                           LETE truncSig:
                                             Bit outSigWidth <-
                                                 RetE ((UniBit (TruncMsb
                                                                  (inSigWidthMinus1 - outSigWidthMinus1)
                                                                  (outSigWidth))
                                                               (castBits _ #leadingOneSig)) >> #subNormDist);
                                           LETE isTruncSigOdd: Bool <-
                                                                    RetE (UniBit (TruncLsb 1 outSigWidthMinus1)
                                                                                 (castBits _ #truncSig) == $1) ;
                                           
                                           LETE sigPlus1 <-
                                                RetE ((#roundingMode_min && #inSign && #inexact)
                                                      || (#roundingMode_max && !#inSign && #inexact)
                                                      || (#roundingMode_near_even && ((#isTailMiddle && #isTruncSigOdd)
                                                                                        ||#isTailGtMiddle))
                                                      || (#roundingMode_near_maxMag && (#isTailMiddle || #isTailGtMiddle)));
                                                      
                                           LETE roundSig : Bit outSigWidth <- RetE (IF #sigPlus1 then #truncSig + $1 else #truncSig);
                                           LETE roundOrJammSig: (Bit outSigWidth) <-
                                                                                  RetE
                                                                                  (IF (#roundingMode_odd && #inexact)
                                                                                   then castBits _ ({< UniBit (TruncMsb 1 outSigWidthMinus1) (castBits _ #roundSig), Const ty WO~1 >})
                                                                                   else #roundSig);
                                           LETE treatedSig: Bit (outSigWidthMinus1) <-
                                                                RetE (IF !(#nfIn @% "isNaN") && #overflow && !#roundToInf (* == roundToMaxMag *)
                                                                      then $$(wones outSigWidthMinus1)
                                                                      else ignoreMsb (#roundOrJammSig << #subNormDist));
                                           
                                           LETE expPlus1RoundSig : Pair (Pair Bool Bool) (Bit outSigWidthMinus1) <-
                                                                        RetE (STRUCT {
                                                                                  "fst" ::= (STRUCT {
                                                                                                 "fst" ::= 
                                                                                                   (IF #subnormal
                                                                                                    then (#truncSig != $0) && ((#roundSig << #subNormDist) == $0)
                                                                                                    else (#truncSig != $0) && (#roundSig == $0)) ;
                                                                                                 "snd" ::= #sigPlus1
                                                                                            });
                                                                                  "snd" ::=  #treatedSig });
                                           RetE #expPlus1RoundSig
                                                  
                                            | _ => RetE (STRUCT {
                                                            "fst" ::= (STRUCT {
                                                                           "fst" ::= $$ false ;
                                                                           "snd" ::= $$ false
                                                                      });
                                                            "snd" ::= castBits _ ({<#inSig, Const ty (wzero (outSigWidthMinus1 - inSigWidthMinus1))>}) })
                                            end;

         LETE expPlus1 : Bool <- RetE (#expSigPlus1RoundSig @% "fst" @% "fst");

         LETE sigRoundedUp : Bool <- RetE (#expSigPlus1RoundSig @% "fst" @% "snd" || (#roundingMode_odd && #inexact));


         LETE roundSig : Bit outSigWidthMinus1 <- RetE (#expSigPlus1RoundSig @% "snd" );

         LETE roundExp : Bit (outExpWidth + 1) <-
                              match Compare_dec.le_dec outExpWidthMinus2 inExpWidthMinus2 with
                              | left isLt1 =>
                                
                                LETE truncExp : Bit (outExpWidth + 1) <-
                                                    RetE (UniBit (TruncLsb (outExpWidth + 1) (inExpWidth - outExpWidth))
                                                                 (castBits _ #inExp));
                                
                                LETE treatedExp : Bit (outExpWidth+1) <-
                                                      RetE (IF #overflow
                                                            then castBits _ (ZeroExtend 2 (Const ty (wones outExpWidthMinus1)))
                                                            else (IF #underflowsToZero
                                                                  then (IF #sigRoundedUp
                                                                        then $1 - $(2 ^ outExpWidthMinus1) - $outSigWidthMinus2
                                                                        else $1 - $(2 ^ outExpWidthMinus1) - $outSigWidthMinus1)
                                                                  else #truncExp));

                                RetE (IF #expPlus1 then (#treatedExp + $1) else #treatedExp)
                                    
                              | right _ => RetE (castBits _ (SignExtend (outExpWidth - inExpWidth) #inExp))
                              end;
         
         LETE unboundedExpPlus1: Bool <-
                match Compare_dec.lt_dec outSigWidthMinus2 inSigWidthMinus2 with
                | left isLt =>
                  LETE truncSig:
                    Bit outSigWidth <-
                        RetE ((UniBit (TruncMsb
                                         (inSigWidthMinus1 - outSigWidthMinus1)
                                         (outSigWidth))
                                      (castBits _ #leadingOneSig)));

                  LETE isTruncSigOdd: Bool <-
                                          RetE ((UniBit (TruncLsb 1 outSigWidthMinus1)
                                                        (castBits _ #truncSig)) == $1) ;
                  LETE tailSigUE <-
                        RetE ((UniBit (TruncLsb
                                         (inSigWidthMinus1 - outSigWidthMinus1)
                                         (outSigWidth))
                                      (castBits _ #leadingOneSig)));
                  LETE isTailMiddleUE <- RetE (#tailSigUE == (castBits _ ({< $$WO~1, $$(wzero (inSigWidthMinus1 - outSigWidth)) >})));
                  LETE isTailGtMiddleUE <- RetE (#tailSigUE > (castBits _ ({< $$WO~1, $$(wzero (inSigWidthMinus1 - outSigWidth)) >})));


                  LETE sigPlus1 <-
                      RetE ((#roundingMode_min && #inSign && (#tailSigUE != $0))
                            || (#roundingMode_max && !#inSign && (#tailSigUE != $0))
                            || (#roundingMode_near_even && ((#isTailMiddleUE && #isTruncSigOdd)
                                                              ||#isTailGtMiddleUE))
                            || (#roundingMode_near_maxMag && (#isTailMiddleUE || #isTailGtMiddleUE)));

                  RetE (IF #sigPlus1
                        then ((#truncSig != $0)
                                && ((#truncSig+$1) == $0)) 
                        else ($$false))
                | _ => RetE ($$ false)
                end;
         
         LETE afterRoundUnderflow <- RetE ((#roundExp <s (* $2 - $(2 ^ outExpWidthMinus1) *) $0 - $ underflowInExpSltMinus)
                                           || !#unboundedExpPlus1
                                                &&(#inExp == ($1 - $(2 ^ outExpWidthMinus1))));

         LETE treatedSubnormal <-
             RetE (IF input @% "afterRounding"
                   then #afterRoundUnderflow
                   else #subnormal);

         LETE underflow <- RetE (#treatedSubnormal && #inexact_underflow);
         

         LETE overflow_afterRound <- RetE (#overflow || (#roundExp >s (* $( 2 ^ outExpWidthMinus1) - $1 *) $overflowExpGlt));

         LETE outNF: NF outExpWidthMinus2 outSigWidthMinus2 <-
                       RetE (STRUCT {
                                 "isNaN"  ::= #nfIn @% "isNaN";
                                 "isInf"  ::= !(#nfIn @% "isNaN") && (#nfIn @% "isInf" ||
                                                                      (!(#nfIn @% "isNaN") && #overflow_afterRound && #roundToInf));
                                 "isZero" ::= !(#nfIn @% "isNaN") && !(# nfIn @% "isInf") && (#nfIn @% "isZero"||
                                                                                              match Compare_dec.le_dec outExpWidthMinus2 inExpWidthMinus2 with
                                                                                              | left _ => #underflowsToZero && !#sigRoundedUp
                                                                                              | right _ => $$ false
                                                                                              end);
                                 "sign"   ::= #nfIn @% "sign";
                                 "sExp"   ::= #roundExp;
                                 "sig"    ::= #roundSig
                               });
         LETE isSignalingNaN <- RetE ((UniBit (TruncMsb _ 1 ) (#nfIn @% "sig")) == $0);

         LETE outFlags: ExceptionFlags <-
                                      RetE (STRUCT {
                                                "invalid"   ::= (#nfIn @% "isNaN") && #isSignalingNaN;
                                                "infinite"  ::= $$false;
                                                "overflow"  ::= #overflow_afterRound && !(#nfIn @% "isInf") && !(#nfIn @% "isNaN") && !(#nfIn @% "isZero");
                                                "underflow" ::= #underflow && !(#nfIn @% "isZero");
                                                "inexact"   ::= #inexact && !(#nfIn @% "isZero")
                                              });

         LETE outNF_final : NF _ _ <-
                              RetE ((#outNF @%[ "sign" <- #outNF @% "sign" && !(#outNF @% "isNaN")]
                                      @%[ "sig" <- IF #outNF @% "isNaN" then {< $$ WO~1, $ 0 >} else #outNF @% "sig"]));

         LETE RoundNF: OpOutput outExpWidthMinus2 outSigWidthMinus2 <-
                               RetE (STRUCT {
                                         "out" ::= #outNF_final;
                                         "exceptionFlags" ::= #outFlags });
         RetE #RoundNF
       );
       abstract lia.
   Defined.


   
   Definition RoundNF_action: ActionT ty (OpOutput outExpWidthMinus2 outSigWidthMinus2) :=
     convertLetExprSyntax_ActionT RoundNF_expr.
   Close Scope kami_action.
   
End RoundAny.

Section RoundDef.
   Variable ty: Kind -> Type.
   Variable inExpWidthMinus2 inSigWidthMinus2: nat.

   Variable outExpWidthMinus2 outSigWidthMinus2: nat. 

   Variable underflowInExpSltMinus underflowToZeroInExpSltMinus overflowExpGlt: nat.
   
   Variable input : (RoundInput inExpWidthMinus2 inSigWidthMinus2) @# ty.

   Local Notation outExpWidthMinus1 := (outExpWidthMinus2 + 1).
   Local Notation outSigWidthMinus1 := (outSigWidthMinus2 + 1).

   Definition RoundNF_def_expr: LetExprSyntax ty (OpOutput outExpWidthMinus2 outSigWidthMinus2) :=
     RoundNF_expr outExpWidthMinus2 outSigWidthMinus2
                  (2 ^ outExpWidthMinus1 - 2)
                  (2 ^ outExpWidthMinus1 + outSigWidthMinus1 - 2)
                  (2 ^ outExpWidthMinus1 - 1)
                  input.
     
   Definition RoundNF_def_action: ActionT ty (OpOutput outExpWidthMinus2 outSigWidthMinus2) :=
     convertLetExprSyntax_ActionT RoundNF_def_expr.
End RoundDef.

Section RoundDef1.
   Variable ty: Kind -> Type.
   Variable inExpWidthMinus2 inSigWidthMinus2: nat.

   Variable outExpWidthMinus2 outSigWidthMinus2: nat. 

   Variable input : (RoundInput inExpWidthMinus2 inSigWidthMinus2) @# ty.

   Variable invalidExc infiniteExc: Bool @# ty.

   Definition RoundRecFN := STRUCT_TYPE
                              { "outNF" :: NF outExpWidthMinus2 outSigWidthMinus2 ;
                                "outFN" :: FN outExpWidthMinus2 outSigWidthMinus2 ;
                                "outRawFloat" :: RawFloat outExpWidthMinus2 outSigWidthMinus2 ;
                                "out" :: RecFN outExpWidthMinus2 outSigWidthMinus2 ;
                                "exceptionFlags" :: ExceptionFlags }.

   Local Open Scope kami_expr.
   Definition RoundNF_to_RecFN_def_expr: LetExprSyntax ty RoundRecFN :=
     LETE inp : NF inExpWidthMinus2 inSigWidthMinus2 <- RetE (input @% "in") ;
       LETE modInput : RoundInput inExpWidthMinus2 inSigWidthMinus2 <- RetE (STRUCT { "in" ::= STRUCT { "isNaN" ::= (invalidExc || (#inp @% "isNaN")) ;
                                                                                                        "isInf" ::= (infiniteExc || (#inp @% "isInf")) ;
                                                                                                        "isZero" ::= #inp @% "isZero" ;
                                                                                                        "sign" ::= #inp @% "sign" ;
                                                                                                        "sExp" ::= #inp @% "sExp" ;
                                                                                                        "sig" ::= #inp @% "sig" } ;
                                                                                      "afterRounding" ::= input @% "afterRounding" ;
                                                                                      "roundingMode" ::= input @% "roundingMode"});
       LETE val: OpOutput outExpWidthMinus2 outSigWidthMinus2 <- RoundNF_def_expr outExpWidthMinus2 outSigWidthMinus2 #modInput;
       LETE valOut : NF outExpWidthMinus2 outSigWidthMinus2 <- RetE (#val @% "out") ;
       LETE valExcept : ExceptionFlags <- RetE (#val @% "exceptionFlags") ;
       LETE final: RecFN outExpWidthMinus2 outSigWidthMinus2 <- RetE (getRecFN_from_NF #valOut);
       LETE valFN : FN outExpWidthMinus2 outSigWidthMinus2 <- RetE (getFN_from_NF #valOut);
       LETE finalVal: RoundRecFN <- RetE (STRUCT { "outNF" ::= #valOut;
                                                   "outFN" ::= #valFN;
                                                   "outRawFloat" ::= (getRawFloat_from_FN #valFN);
                                                   "out" ::= #final;
                                                   "exceptionFlags" ::= STRUCT {"invalid" ::= invalidExc ;
                                                                                "infinite" ::= infiniteExc ;
                                                                                "overflow" ::= #valExcept @% "overflow" ;
                                                                                "underflow" ::= #valExcept @% "underflow" ;
                                                                                "inexact" ::= #valExcept @% "inexact" }});
       RetE #finalVal.
   Local Close Scope kami_expr.
End RoundDef1.
