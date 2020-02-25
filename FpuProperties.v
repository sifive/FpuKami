Require Import Kami.AllNotations FpuKami.Definitions FpuKami.Classify FpuKami.ModClassify.

Section Compat.


  Set Implicit Arguments.

End Compat.
    
  
Section Properties.
  Variable expWidthMinus2 sigWidthMinus2: nat.
  
  Local Notation expWidthMinus1 := (expWidthMinus2 + 1).
  Local Notation expWidth := (expWidthMinus1 + 1).

  Local Notation sigWidthMinus1 := (sigWidthMinus2 + 1).
  Local Notation sigWidth := (sigWidthMinus1 + 1).

  Variable expWidth_prop: expWidthMinus2 >= 2.

  Variable expWidthMinus2_plus4_gt_sigWidth: 2 ^ expWidthMinus2 + 4 > sigWidth.

  Lemma expWidth_ge_sigWidth:
    2 ^ expWidthMinus1 > sigWidth.
  Proof.
    rewrite ?Nat.pow_add_r; simpl.
    assert (sth: 2 ^ expWidthMinus2 >= 4). {
      pose proof (@Nat.pow_le_mono_r 2 _ _ ltac:(lia) expWidth_prop).
      assumption.
    }
    lia.
  Qed.

  Section FN.
    Variable fn: FN expWidthMinus2 sigWidthMinus2 @# type.

    Ltac simplifyEvalExpr :=
      cbn [evalExpr map evalCABool evalUniBool evalUniBit fold_left Vector.nth Vector.caseS snd evalConstT
                    Vector_nth_map2_r Vector_nth_map2_r' Fin.t_rect projT2 evalCABit pack evalBinBit combine isEq projT1 Kind_rect
                    ZeroExtend countLeadingZeros ConstExtract

                    nth_Fin nth_Fin_map2 eq_add_S f_equal (* map_length_red hedberg *)

                    getRecFN_from_FN getRawFloat_from_RecFN getRawFloat_from_FN getRecFN_from_RawFloat

                    sign infOrNaN isZeroExpIn isZeroFractIn isNaN fracMsb isSNaN

                    normDist subnormFract adjustedExp isZero isSpecialMsb isSpecialLsb isSpecial

                    isZeroNaNInf0 isZeroNaNInf1 isZeroNaNInf2 isZeroRecFN isNaN_or_Inf get_exp_from_RecFN

                    sExp_expWidth sExp_expWidthMinus1 sExp_expWidthMinus2

                    isFiniteNonzero isSubnormal isSigNaNRawFloat_frac isSigNaNRawFloat
          ];
      repeat rewrite ?andb_true_l, ?andb_true_r, ?andb_false_r, ?andb_false_l.

    Ltac simplifyEvalExpr_hyp H :=
      cbn [evalExpr map evalCABool evalUniBool evalUniBit fold_left Vector.nth Vector.caseS snd evalConstT
                    Vector_nth_map2_r Vector_nth_map2_r' Fin.t_rect projT2 evalCABit pack evalBinBit combine isEq projT1 Kind_rect
                    ZeroExtend countLeadingZeros ConstExtract

                    nth_Fin nth_Fin_map2 eq_add_S f_equal (* map_length_red hedberg *)

                    getRecFN_from_FN getRawFloat_from_RecFN getRawFloat_from_FN getRecFN_from_RawFloat

                    sign infOrNaN isZeroExpIn isZeroFractIn isNaN fracMsb isSNaN

                    normDist subnormFract adjustedExp isZero isSpecialMsb isSpecialLsb isSpecial

                    isZeroNaNInf0 isZeroNaNInf1 isZeroNaNInf2 isZeroRecFN isNaN_or_Inf get_exp_from_RecFN

                    sExp_expWidth sExp_expWidthMinus1 sExp_expWidthMinus2

                    isFiniteNonzero isSubnormal isSigNaNRawFloat_frac isSigNaNRawFloat
          ] in H;
      repeat rewrite ?andb_true_l, ?andb_true_r, ?andb_false_r, ?andb_false_l in H.
    
    Lemma isSpecial_infOrNaN: evalExpr (isSpecial fn) = evalExpr (infOrNaN fn).
    Proof.
      pose proof expWidth_ge_sigWidth as expWidth_ge_sigWidth.
      simpl.
      match goal with
      | |- _ = getBool ?P => destruct P; [rewrite e; simpl in *|]
      end.
      - simpl.
        destruct (weq _ (wones expWidth) (natToWord expWidth 0)); simpl.
        + pose proof (@wzero_wones expWidth ltac:(lia)).
          congruence.
        + (* unfold wzero. *)
          rewrite wplus_unit.
          simpl.
          (* a dirty solution, but a solution... *)
          assert (ZToWord 0 0 = natToWord 0 0) by auto; rewrite !H; clear H.
          assert (ZToWord 1 0 = natToWord 1 0) by auto; rewrite !H; clear H.
          (* assert (ZToWord 1 1 = natToWord 1 1) by auto; rewrite !H; clear H. *)
          (* assert (ZToWord expWidthMinus1 1 = natToWord _ 1) by auto; rewrite !H; clear H. *)
          rewrite combine_wones_WO; [|unfold wzero; intro].
          * simpl.
            
            rewrite split1_combine_wplus.
            match goal with
            | |- getBool (weq _ (truncMsb (_ ^+ ?P)) _) = true => rewrite <- (natToWord_wordToNat _ P)
            end.
            
            
            rewrite !wordToNat_combine; try lia.
            rewrite Nat.pow_0_r, Nat.mul_1_l.
            simpl.
            rewrite Nat.mul_1_r.
            rewrite wordToNat_natToWord_idempotent'.
            -- rewrite wones_natToWord.
               
               rewrite <- natToWord_plus.
               simpl.
               assert (sth: 2 ^ expWidth - 1 + S (2 ^ expWidthMinus1) = 2 ^ expWidth + 2 ^ expWidthMinus1) by (pose proof (one_le_pow2 expWidth); lia).
               rewrite sth.
               match goal with
               | |- getBool (weq _ ?P _) = true => 
                 rewrite <- (natToWord_wordToNat _ P)
               end.
               
               rewrite wordToNat_split2.
               assert (sth2: 2 ^ expWidth + 2 ^ expWidthMinus1 = 2 ^ expWidthMinus1 + 2 ^ expWidth) by lia.
               rewrite sth2.
               
               rewrite natToWord_pow2_add.
               rewrite wordToNat_natToWord_idempotent'.
               ** rewrite Nat.div_same; auto.
                  pose proof (pow2_zero expWidthMinus1).
                  lia.
               ** apply (Nat.pow_lt_mono_r 2 expWidthMinus1 expWidth); try lia.
            -- assert (sth: expWidthMinus2 + 1 = S expWidthMinus2) by lia.
               rewrite sth.
               apply one_lt_pow2.
          * apply (f_equal (@truncMsb 1 _)) in H.
            
            rewrite split2_combine in *.
            
            rewrite split2_zero in *.
            unfold natToWord in H; simpl in *.
            discriminate.
      - simpl.
        cbn [natToWord].
        rewrite ?wplus_unit.
        match goal with
        | |- context [weq _ ?P (natToWord expWidth 0)] => remember P as f; simpl in f
        end.
        assert (sth3: wordToNat _ f <> 2 ^ expWidth - 1). {
          intro.
          apply (f_equal (natToWord expWidth)) in H.
          rewrite natToWord_wordToNat in H.
          rewrite <- wones_natToWord in H.
          subst.
          tauto.
        }
        
        assert (sth: wordToNat _ f < 2 ^ expWidth - 1). {
          pose proof (wordToNat_bound f).
          lia.
        }
        clear sth3 Heqf.
        destruct (weq _ f (natToWord expWidth 0)); subst; simpl.
        + unfold normDist.
          rewrite ?evalExpr_countLeadingZeros.
          simpl.
          rewrite andb_false_iff; left.
          assert (sth2: 2 ^ expWidthMinus1 > sigWidthMinus1) by lia.
          assert (sth2_5: 2 ^ (expWidth + 1) > sigWidthMinus1) by (assert (helper: expWidth + 1 = 2 + expWidthMinus1) by lia; rewrite helper; simpl; lia).
          match goal with
          | |- context[countLeadingZerosWord _ _ ?P] =>
            pose proof (countLeadingZerosWord_le_len _ sth2_5 P)
          end.
          match goal with
          | |- getBool (weq _ ?P _) = false => rewrite <- (natToWord_wordToNat _ P)
          end.
          rewrite ?wordToNat_split2; simpl.
          repeat match goal with
          | |- context [wconcat ?P ?Q] => rewrite <- (natToWord_wordToNat _ (wconcat P Q)); rewrite wordToNat_combine; simpl
          end.
          rewrite ?Nat.mul_1_r, ?Nat.mul_0_r, ?Nat.add_0_r.
          rewrite ?wordToNat_natToWord_idempotent'.
          * rewrite Nat.div_small; simpl; auto.
            (* simpl; rewrite Z.mod_small; try split; try lia; simpl.
            2:{ rewrite <- Z.pow_1_r at 1.
                apply Z.pow_lt_mono_r; lia. } *)
            (* pre_word_omega. *)
            match goal with
            | |- context [weq _ ?w1 ?w2] => destruct (weq _ w1 w2); simpl
            end.
            ** assert (sth3: 2 ^ (expWidth+1) = 2 ^ (expWidthMinus1) + 2 ^ (expWidthMinus1) + 2 ^ expWidth) by (rewrite ?Nat.add_1_r; simpl; lia).
              rewrite wplus_comm.
              rewrite wneg_wnot.
              rewrite wminus_def.
              rewrite <- wneg_wplus_distr.
              replace (ZToWord (expWidth + 1) 1) with (natToWord (expWidth + 1) 1); auto.
              rewrite <- natToWord_plus.
              (* assert (sth_tmp : (1 = Z.of_nat 1)%Z) by auto.
              rewrite sth_tmp; rewrite <- Nat2Z.inj_add; clear sth_tmp.*)
              rewrite <- wminus_def.
              rewrite wminus_minus.
              (* rewrite Nat2Z_ZToWord.*)
              apply lt_minus'.
              rewrite ?wordToNat_natToWord_idempotent'; lia.
              rewrite wordToNat_natToWord_idempotent'.
              rewrite Nat.pow_add_r; simpl; lia.
              do 2 rewrite Nat.pow_add_r; simpl. lia.
              rewrite wordToNat_natToWord_idempotent'.
              assert (sth4: 2 ^ expWidth = 2 ^ (expWidthMinus1) + 2 ^ (expWidthMinus1) ).
              rewrite ?Nat.add_1_r; simpl; lia.
              rewrite sth4.
              do 2 rewrite <- Nat.add_1_r.
              rewrite Plus.plus_assoc_reverse.
              apply Plus.plus_lt_compat_l.
              lia.
              rewrite sth3.
              rewrite Plus.plus_assoc_reverse.
              do 2 rewrite <- Nat.add_1_r.
              rewrite Plus.plus_assoc_reverse.
              apply Plus.plus_lt_compat_l.
              lia.
              simpl.
              unfold wltu. unfold natToWord.
              rewrite !wordToZ_ZToWord; try split; try rewrite <- Zpow_of_nat; try lia.
              apply Z.ltb_lt; apply Nat2Z.inj_lt; lia.
            ** unfold wleu, natToWord in H. 
               rewrite wordToZ_ZToWord in H by (rewrite <- Zpow_of_nat; lia).
               assert (sth3: sigWidthMinus1 < 2 ^ expWidthMinus1 - 1) by lia.
               rewrite wordToNat_wplus.
               rewrite wordToNat_wnot.
               rewrite wordToNat_natToWord_idempotent'.
                 -- simpl in *.
                    apply Z.leb_le in H.
                    apply Z2Nat.inj_le in H; try apply wordVal_pos; try lia.
                    rewrite Nat2Z.id in H.
                    unfold wordToNat.
                    match type of H with
                    | ?P <= _ => remember P as rem
                    end.
               assert (sth4: 2 ^ (expWidth + 1) > rem). {
                 assert (helper: expWidth + 1 = 2 + expWidthMinus1) by lia.
                 rewrite helper.
                 simpl; lia.
               }
               pose proof (one_le_pow2 (expWidth + 1)) as sth5.
               assert (sth6: rem < 2 ^ expWidthMinus1) by lia.
               assert (sth7: 2 ^ (expWidth + 1) - rem - 1 + S (S (2 ^ expWidthMinus1)) = 2 ^ (expWidth + 1) + (S (2 ^ expWidthMinus1) - rem)) by lia.
               rewrite sth7.
               rewrite Nat.add_mod by lia.
               rewrite Nat.mod_same by lia; simpl.
               destruct rem; simpl; rewrite ?Nat.mod_mod by lia; rewrite Nat.mod_small;
                 rewrite ?(Nat.pow_add_r _ expWidthMinus1 1); simpl; try nia.
               ++ assert (sth8: expWidth + 1 = 2 + expWidthMinus1) by lia; rewrite sth8; simpl; nia.
               ++ assert (sth8: expWidth + 1 = 2 + expWidthMinus1) by lia; rewrite sth8; simpl; nia.
            -- rewrite ?Nat.pow_add_r; simpl.
               pose proof (zero_lt_pow2 expWidthMinus2).
               lia.
                 * rewrite <- Nat.pow_1_r at 1.
                   apply Nat.pow_lt_mono_r; lia.
                 * unfold wordToNat. simpl.
                   apply Nat2Z.inj_lt.
                   rewrite Z2Nat.id.
                   rewrite Zpow_of_nat.
                   apply Z_mod_lt.
                   rewrite <- Zpow_of_nat. lia.
                   apply Z.mod_pos_bound.
                   rewrite <- Zpow_of_nat. lia.
                 * unfold wordToNat. simpl.
                   rewrite Z2Nat.id.
                   rewrite Z.mod_mod.
                   rewrite Z.mod_small.
                   rewrite !pow2_add_mul.
                   simpl.
                   assert (sth3: 2 < 2 ^ expWidthMinus2).
                   rewrite <- Nat.pow_1_r at 1.
                   apply Nat.pow_lt_mono_r; lia.
                   lia.
                   split; try lia.
                   apply Z2Nat.inj_lt; try lia.
                   apply Z.pow_nonneg; lia.
                   rewrite <- Zpow_of_nat, Nat2Z.id.
                   assert (th: Z.to_nat 2 = 2); auto; rewrite th; clear th.
                   rewrite <- Nat.pow_1_r at 1.
                   apply Nat.pow_lt_mono_r; lia.
                   apply Z.pow_nonzero; lia.
                   apply Z.mod_pos_bound.
                   apply Z.pow_pos_nonneg; lia.
                 * auto.
                 * auto.
                 * auto.
        + rewrite <- (natToWord_wordToNat _ (wconcat (natToWord 1 0) f)).
          rewrite <- (natToWord_wordToNat _ (wconcat (ZToWord 1 0)
            (wconcat (ZToWord 1 1) (wconcat (ZToWord expWidthMinus1 1) (ZToWord 0 0))))).
          rewrite ?wordToNat_combine; auto.
          simpl.
          rewrite ?Nat.mul_0_r, ?Nat.add_0_r, ?Nat.mul_1_r.
          rewrite wordToNat_natToWord_idempotent' with (n := 1) by lia.
          rewrite <- natToWord_plus.
          match goal with
          | |- getBool (weq _ ?P _) && getBool (weq _ ?Q _) = false => rewrite <- (natToWord_wordToNat _ P);
                                                                     rewrite <- (natToWord_wordToNat _ Q)
          end.
          rewrite ?wordToNat_split2; simpl.
          rewrite wordToNat_split1; simpl.
          assert (sth1: 2 ^ expWidth >= 1) by lia.
          assert (sth2: wordToNat _ f + S (2 ^ expWidthMinus1) < 2 ^ (expWidth + 1)). {
            assert (sth3: S expWidth = expWidth + 1) by lia; rewrite <- sth3; simpl.
            assert (sth4: 2 ^ (S expWidthMinus1) = 2 ^ expWidth) by (f_equal; lia).
            rewrite <- sth4 in *; simpl.
            simpl in *.
            lia.
          }
          rewrite ?wordToNat_natToWord_idempotent' by auto.
          rewrite andb_false_iff.
          assert (sth3: 2 ^ expWidthMinus1 >= 1) by lia.
          assert (sth4: 2 ^ expWidth = 2 ^ (S expWidthMinus1)) by (f_equal; lia).
          destruct (Compare_dec.le_lt_dec (2 ^ expWidthMinus1-1) (wordToNat _ f)); [ right | left ].
          * rewrite mod_sub'; simpl; rewrite ?Nat.add_0_r; try nia.
            -- rewrite Nat.div_small; simpl; auto.
               rewrite sth4 in *; simpl in *.
               nia.
            -- rewrite sth4; simpl.
               nia.
          * rewrite Nat.div_small; simpl; auto.
            rewrite sth4; simpl.
            lia.
    Qed.

    Lemma isZero_not_isNaN: evalExpr (isZero fn) = true -> evalExpr (isNaN fn) = false.
    Proof.
      pose proof expWidth_ge_sigWidth as expWidth_ge_sigWidth.
      intros.
      apply andb_prop in H; dest.
      apply andb_false_intro1.
      simpl in *.
      match goal with
      | H: getBool (weq _ ?P ?Q) = true |- getBool (weq _ ?P ?R) = false => destruct (weq _ P Q) as [p|q]; [rewrite p; simpl |]
      end.
      - destruct (weq _ (natToWord expWidth 0) (wones expWidth)); auto.
        exfalso.
        apply wzero_wones in e; auto.
        lia.
      - simpl in *; discriminate.
    Qed. 

    Lemma isZero_not_infOrNaN: evalExpr (isZero fn) = true -> evalExpr (infOrNaN fn) = false.
    Proof.
      pose proof expWidth_ge_sigWidth as expWidth_ge_sigWidth.
      simpl.
      intros.
      apply andb_prop in H; dest.
      match type of H with
      | getBool ?P = true => destruct P; [| discriminate]
      end.
      rewrite e.
      match goal with
      | |- getBool ?P = false => destruct P; auto
      end.
      pose proof (@wzero_wones expWidth ltac:(lia)).
      tauto.
    Qed.

    Lemma infOrNaN_not_isZero: evalExpr (infOrNaN fn) = true -> evalExpr (isZero fn) = false.
    Proof.
      pose proof isZero_not_infOrNaN.
      intros.
      destruct (evalExpr (isZero fn)); [|auto].
      specialize (H eq_refl).
      congruence.
    Qed.

    Lemma infOrNaN_sExp_expWidthMinus2':
      evalExpr (infOrNaN fn) = true -> getBool (weq _ (evalExpr (sExp_expWidthMinus2 (getRawFloat_from_FN fn))) WO~0) = true.
    Proof.
      pose proof expWidth_ge_sigWidth as expWidth_ge_sigWidth.
      simpl.
      rewrite ?split1_combine.
      intros.
      match type of H with
      | getBool ?P = _ => destruct P
      end; simpl in *; [clear H; rewrite e; clear e| discriminate].
      destruct (weq _ (wones expWidth) (natToWord expWidth 0)); simpl; [pose proof (@wzero_wones expWidth ltac:(lia)); congruence| clear n].
      rewrite wzero_wplus.
      match goal with
      | |- getBool (weq _ (@truncMsb _ _ (@truncLsb _ _ (@truncLsb _ _ ?P))) _) = true =>
        rewrite <- (natToWord_wordToNat _ P)
      end.
      rewrite wordToNat_wplus.
      rewrite ?wordToNat_combine.
      simpl.
      rewrite ?Nat.mul_0_r, ?Nat.add_0_r, ?Nat.mul_1_r.
      rewrite wones_pow2_minus_one.
      rewrite wordToNat_natToWord_idempotent' by lia.
      assert (sth0: expWidth + 1 = S expWidth) by lia.
      assert (sth1: expWidth = S expWidthMinus1) by lia.
      assert (sth2: 2 ^ expWidth >= 1) by (rewrite sth1; pose proof (one_lt_pow2 expWidthMinus1); lia).
      assert (sth3: 2 ^ expWidth - 1 + (1 + 2 ^ expWidthMinus1) = 2 ^ expWidth + 2 ^ expWidthMinus1) by lia.
      rewrite sth3.
      rewrite Nat.mod_small by (rewrite sth0, sth1; simpl; lia).
      match goal with
      | |- getBool (weq _ (@truncMsb _ _ (@truncLsb _ _ ?P)) _) = _ =>
        rewrite <- (natToWord_wordToNat _ P)
      end.
      rewrite wordToNat_split1.
      rewrite wordToNat_natToWord_idempotent' by (rewrite sth0, sth1; simpl; lia).
      assert (sth4: 2 ^ expWidth + 2 ^ expWidthMinus1 = 2 ^ expWidthMinus1 + 1 * 2 ^ expWidth) by lia.
      rewrite sth4.
      rewrite Nat.mod_add by lia.
      rewrite Nat.mod_small by (rewrite sth1; simpl; lia).
      match goal with
      | |- getBool (weq _ (@truncMsb _ _ ?P) _) = _ =>
        rewrite <- (natToWord_wordToNat _ P)
      end.
      rewrite wordToNat_split1.
      rewrite wordToNat_natToWord_idempotent' by (rewrite sth1; simpl; lia).
      rewrite Nat.mod_same by lia.
      match goal with
      | |- getBool (weq _ ?P _) = _ =>
        rewrite <- (natToWord_wordToNat _ P)
      end.
      rewrite wordToNat_split2.
      rewrite wordToNat_natToWord_idempotent' by lia.
      rewrite Nat.div_0_l by (pose proof (zero_lt_pow2 expWidthMinus2); lia).
      auto.
      auto.
      auto.
      auto.
      auto.
    Qed.

    Lemma infOrNaN_sExp_expWidthMinus2:
      evalExpr (infOrNaN fn) = true -> evalExpr (sExp_expWidthMinus2 (getRawFloat_from_FN fn)) = WO~0.
    Proof.
      intros H.
      apply infOrNaN_sExp_expWidthMinus2' in H.
      destruct (weq _ (evalExpr (sExp_expWidthMinus2 (getRawFloat_from_FN fn))) WO~0); [auto|discriminate].
    Qed.

    Lemma isNaN_or_Inf_infOrNaN:
      evalExpr (isNaN_or_Inf (getRecFN_from_FN fn)) = evalExpr (infOrNaN fn).
    Proof.
      pose proof isZero_not_infOrNaN as sth.
      rewrite <- isSpecial_infOrNaN in *.
      simpl.
      simpl in sth.
      match type of sth with
      | ?P = true -> ?Q => case_eq P; simpl in *; intros H; [specialize (sth H); auto| clear sth; rewrite ?wzero_wplus]
      end.
      rewrite ?split1_combine.
      auto.
    Qed.
    
    Lemma infOrNaN_isZeroNaNInf2_0_isZeroFractIn:
      evalExpr (infOrNaN fn) = true -> getBool (weq _ (evalExpr (isZeroNaNInf2 (getRecFN_from_FN fn))) WO~0) = evalExpr (isZeroFractIn fn).
    Proof.
      intros sth1.
      pose proof isSpecial_infOrNaN as sth2.
      pose proof (infOrNaN_sExp_expWidthMinus2 sth1) as sth3.
      simpl in *.
      rewrite sth3.
      rewrite sth2.
      rewrite sth1.
      clear sth2 sth3.
      rewrite if_same.
      rewrite wor_wzero.
      rewrite andb_true_l.
      match goal with
      | |- _ = ?P => destruct P; simpl; auto
      end.
    Qed.

    Lemma infOrNaN_isZeroNaNInf2_1_isZeroFractIn:
      evalExpr (infOrNaN fn) = true -> getBool (weq _ (evalExpr (isZeroNaNInf2 (getRecFN_from_FN fn))) WO~1) = negb (evalExpr (isZeroFractIn fn)).
    Proof.
      intros sth1.
      pose proof isSpecial_infOrNaN as sth2.
      pose proof (infOrNaN_sExp_expWidthMinus2 sth1) as sth3.
      simpl in *.
      rewrite sth3.
      rewrite sth2.
      rewrite sth1.
      rewrite if_same.
      rewrite wor_wzero.
      rewrite andb_true_l.
      match goal with
      | |- _ = ?P => destruct P; simpl; auto
      end.
    Qed.

    Lemma RawFloat_RecFN_FN_isNaN:
      evalExpr (getRawFloat_from_RecFN (getRecFN_from_FN fn)) Fin.F1 = evalExpr (getRawFloat_from_FN fn) Fin.F1.
    Proof.
      pose proof isNaN_or_Inf_infOrNaN as sth1.
      pose proof infOrNaN_isZeroNaNInf2_0_isZeroFractIn as sth2.
      pose proof isSpecial_infOrNaN as sth3.
      Opaque isNaN_or_Inf infOrNaN isZeroNaNInf2 isZeroFractIn isSpecial.
      simpl.
      rewrite sth1, sth3.
      destruct (evalExpr (infOrNaN fn)); simpl; auto.
      unfold natToWord; simpl.
      rewrite <- sth2; auto.
      match goal with
      | |- getBool ?P = negb (getBool ?Q) => case_eq P; case_eq Q; intros; simpl in *; auto
      end.
      - clear - e e0; rewrite e in e0; discriminate.
      - clear - n n0. exfalso; eapply word1_neq; eauto.
        Transparent isNaN_or_Inf infOrNaN isZeroNaNInf2 isZeroFractIn isSpecial.
    Qed.

    Lemma RawFloat_RecFN_FN_isInf:
      evalExpr (getRawFloat_from_RecFN (getRecFN_from_FN fn)) (Fin.FS Fin.F1) = evalExpr (getRawFloat_from_FN fn) (Fin.FS Fin.F1).
    Proof.
      pose proof isNaN_or_Inf_infOrNaN as sth1.
      pose proof infOrNaN_isZeroNaNInf2_0_isZeroFractIn as sth2.
      pose proof isSpecial_infOrNaN as sth3.
      Opaque isNaN_or_Inf infOrNaN isZeroNaNInf2 isZeroFractIn isSpecial.
      simpl.
      rewrite sth1, sth3.
      destruct (evalExpr (infOrNaN fn)); simpl; auto.
      Transparent isNaN_or_Inf infOrNaN isZeroNaNInf2 isZeroFractIn isSpecial.
    Qed.

    Lemma RawFloat_RecFN_FN_sign:
      evalExpr (getRawFloat_from_RecFN (getRecFN_from_FN fn)) (Fin.FS (Fin.FS (Fin.FS Fin.F1))) = evalExpr (getRawFloat_from_FN fn) (Fin.FS (Fin.FS (Fin.FS Fin.F1))).
    Proof.
      auto.
    Qed.

    (* copy-pasted from bbv, commit b98e19b *)

    Lemma isZeroRecFN_isZero:
      evalExpr (isZeroRecFN (getRecFN_from_FN fn)) = evalExpr (isZero fn).
    Proof.
      Opaque isNaN_or_Inf infOrNaN isZeroFractIn isSpecial normDist subnormFract isZeroExpIn.
      simpl in *.
      match goal with
      | |- _ = ?P => case_eq P; intros; simpl; auto
      end.
      - rewrite isSpecial_infOrNaN.
        pose proof isZero_not_infOrNaN as hyp2.
        simpl in *.
        specialize (hyp2 H).
        rewrite hyp2.
        auto.
      - rewrite wor_wzero.
        rewrite ?split1_combine.
        rewrite isSpecial_infOrNaN.
        case_eq (evalExpr (isZeroExpIn fn)); intros hyp; rewrite hyp in *; simpl in *.
        + rewrite H in *; simpl; rewrite andb_true_r.
          rewrite ?wzero_wplus.
          Transparent isZeroExpIn infOrNaN.
          simpl in *.
          match type of hyp with
          | getBool ?P = true => destruct P; [|discriminate]
          end.
          rewrite e.
          pose proof (@wzero_wones expWidth ltac:(lia)).
          match goal with
          | |- context [if getBool ?P then _ else _] => destruct P; [tauto|simpl; rewrite wzero_wor]
          end.
          match goal with
          | |- context [wnot _ ?P] => rewrite <- (natToWord_wordToNat _ (wnot _ P))
          end.
          rewrite ?wordToNat_wnot.
          match goal with
          | |- context [wconcat ?P ?Q] => (rewrite <- (natToWord_wordToNat _ (wconcat P Q)))
          end.
          rewrite ?wordToNat_combine; simpl.
          rewrite ?Nat.mul_1_r, ?Nat.mul_0_r, ?Nat.add_0_r.
          rewrite wordToNat_natToWord_idempotent'.
          * rewrite <- ?natToWord_plus.
            match goal with
            | |- context[?A - wordToNat _ (?B) - 1 + (2 + ?P)] => pose proof (wordToNat_bound B) as sth0;
                                                         assert (sth1: A > wordToNat _ B) by lia;
                                                         assert (sth2: A - wordToNat _ B - 1 + (2 + P) = A + P + 1 - wordToNat _ B) by lia; rewrite ?sth2;
                                                           remember B as val
            end.
            Transparent normDist.
            unfold normDist in Heqval.
            simpl in Heqval.
            match goal with
            | [H: val = if getBool (weq _ ?w1 ?w2) then _ else _ |- _] => destruct (weq _ w1 w2); simpl in *
            end.
            ***
               subst.
               assert (sth3: 2 ^ (expWidth + 1) + 2 ^ expWidthMinus1 + 1 - sigWidthMinus2 = 2 ^ (expWidth + 1) + (2 ^ expWidthMinus1 + 1 - sigWidthMinus2)). {
                 pose proof expWidth_ge_sigWidth.
                 rewrite Nat.add_sub_assoc; lia.
               }
               assert (sigWidthMinus2 < 2 ^ (expWidth + 1)). {
                 rewrite ?Nat.pow_add_r; simpl.
                 rewrite ?Nat.pow_add_r; simpl.
                 pose proof (pow2_zero expWidthMinus2).
                 nia.
               }
               destruct Compare_dec.le_lt_dec with sigWidthMinus2 1 as [sig_le_2 | sig_gt_2].
               apply andb_false_intro1.
               apply andb_false_intro2.
               rewrite <- wmsb_true_split2_wones with (b:=false).
               simpl; auto.
               
               rewrite wordToNat_natToWord_idempotent'; auto.
               rewrite sth3.
               rewrite natToWord_plus.
               rewrite pow2_wzero.
               rewrite wzero_wplus.
               rewrite split1_fits_natToWord.
               rewrite Nat.add_1_r.
               apply wmsb_1_natToWord.
               split; auto.
               lia.
               pose proof expWidth_ge_sigWidth.
               apply lt_minus'; lia.
               pose proof expWidth_ge_sigWidth.
               apply lt_minus'. lia.
               rewrite Nat.add_1_r.
               simpl; lia.
               rewrite ?Nat.add_1_r.
               rewrite <- Nat.add_1_r.
               simpl.
               apply Plus.plus_lt_compat_l.
               rewrite ?Nat.add_0_r.
               rewrite <- mul2_add. 
               replace (2 ^ expWidthMinus2 * 2) with (2 ^ expWidthMinus2 * 2 ^ 1) by (simpl;reflexivity).
               rewrite <- Nat.pow_add_r.
               lia.

               apply andb_false_intro2.
               rewrite <- wmsb_true_split2_wones with (b:=false).
               simpl; auto.
               rewrite wordToNat_natToWord_idempotent'; auto.
               rewrite sth3.
               rewrite natToWord_plus.
               rewrite pow2_wzero.
               rewrite wzero_wplus.
               rewrite split1_fits_natToWord.
               rewrite Nat.add_1_r.
               assert (sth4: 2 ^ (S expWidthMinus2) + 1 - sigWidthMinus2 < 2 * 2 ^ expWidthMinus2). { 
                 rewrite Nat.add_comm.
                 rewrite <- Nat.add_sub_assoc.
                 rewrite Nat.add_comm.
                 assert (sth4: 2 * 2 ^ expWidthMinus2 = 2 ^ (S expWidthMinus2)). {
                   assert (2 ^ 1 = 2). auto.
                   rewrite <- H2 at 1.
                   rewrite <- pow2_add_mul.
                   rewrite <- Nat.add_1_r. auto.
                 }
                 destruct sigWidthMinus2 as [| sigWidthMinus3] eqn:Heq; [inversion sig_gt_2|].
                 destruct sigWidthMinus3 as [| sigWidthMinus4] eqn:Heq1; [lia|].
                 rewrite sth4.
                 replace (S (S sigWidthMinus4)) with (sigWidthMinus4 + 1 + 1) by lia.
                 rewrite Nat.sub_add_distr.
                 replace (2 ^ (S expWidthMinus2) - (sigWidthMinus4 + 1) - 1 + 1) with (2 ^ (S expWidthMinus2) - (sigWidthMinus4 + 1)) by lia. 
                 rewrite <- Heq in *.
                 pose proof expWidth_ge_sigWidth.
                 apply Nat.sub_lt; lia.
                 pose proof expWidth_ge_sigWidth.
                 rewrite ?Nat.pow_add_r; simpl.
                 lia.
               }
               rewrite split1_fits_natToWord; auto.
               apply wmsb_1_natToWord.
               split; auto.
               simpl.
               assert (sth5: 
                         2 ^ expWidthMinus2 + (2 ^ expWidthMinus2 + 0) + 1 - sigWidthMinus2 =
                         
                         2 ^ expWidthMinus2 + ((2 ^ expWidthMinus2 + 0) + 1 - sigWidthMinus2)). {
                 pose proof expWidth_ge_sigWidth.
                 rewrite Nat.add_sub_assoc; lia.
               }
               rewrite sth5.
               rewrite <- Nat.add_0_r at 1.
               apply Plus.plus_le_compat_l.
               lia.
               apply lt_minus'; try lia.
               rewrite Nat.add_1_r.
               simpl.
               rewrite ?Nat.add_1_r.
               simpl.
               lia.
               rewrite ?Nat.add_1_r.
               simpl.
               lia.
            *** rewrite evalExpr_countLeadingZeros in Heqval.
            pose proof expWidth_ge_sigWidth as sth3.
            assert (sth4: 2 ^ (expWidth + 1) > sigWidthMinus1). {
              rewrite ?Nat.pow_add_r; simpl.
              pose proof (pow2_zero expWidthMinus2).
              nia.
            }
            simpl in *.
            Transparent isZeroFractIn.
            simpl in H.
            match type of H with
            | getBool ?P = false => destruct P; [discriminate|]
            end.
            match type of Heqval with
            | _ = countLeadingZerosWord _ _ ?P =>
              pose proof (countLeadingZerosWord_lt_len _ sth4 n0) as sth5
            end.
            rewrite <- Heqval in sth5.
            apply wordToNat_lt1 in sth5.
            rewrite wordToNat_natToWord_idempotent' in sth5 by assumption.
            assert (sth6: 2 ^ (expWidth + 1) + 2 ^ expWidthMinus1 + 1 - wordToNat _ val >= 2 ^ (expWidth + 1) + 2 ^ expWidthMinus1 - 2 ^ expWidthMinus2) by lia.
            remember (2 ^ (expWidth + 1) + 2 ^ expWidthMinus1 + 1 - wordToNat _ val) as val2.
            repeat match goal with
                   | |- context[weq _ (@truncMsb ?A ?B ?P) _] =>
                     rewrite <- (natToWord_wordToNat _ (@truncMsb A B P))
                   | |- context[weq _ (@truncLsb ?A ?B ?P) _] =>
                     rewrite <- (natToWord_wordToNat _ (@truncLsb A B P))
                   end.
            assert (sth7: val2 <= 2 ^ (expWidth + 1) + 2 ^ expWidthMinus1 + 1) by lia.
            rewrite ?wordToNat_split2, ?wordToNat_split1.
            rewrite mod_factor' with (c := 2).
            -- rewrite <- andb_assoc.
               rewrite andb_false_iff; right.
               assert (sth8: val2 >= 2 ^ (expWidth + 1)) by lia.
               assert (sth9: val2 >= 2 * 2 ^ expWidth) by (rewrite Nat.pow_add_r in sth8; simpl in sth8; nia).
               assert (sth10: val2 >= 4 * 2 ^ (expWidthMinus1)) by (do 2 (rewrite Nat.pow_add_r in sth8); simpl in sth8; nia).
               rewrite ?wordToNat_natToWord_eqn.
               rewrite mod_factor' with (c := 2) by (pose proof (pow2_zero expWidth); try lia; rewrite ?Nat.pow_add_r; auto).
               rewrite mod_factor' with (c := (2 * 2)).
               ++ pose proof (pow2_zero expWidth) as sth11.
                  pose proof (pow2_zero expWidthMinus1) as sth12.
                  rewrite <- mod_sub with (b := 2) by auto. 
                  rewrite <- mod_sub with (a := val2) (b := 4) by auto.
                  rewrite Nat.mod_small.
                  ** assert (sth13: 2 ^ expWidthMinus1 - 2 ^ expWidthMinus2 <= val2 - 2 ^ (expWidth + 1) <= 2 ^ expWidthMinus1 + 1) by lia.
                     destruct (Compare_dec.le_lt_dec (val2 - 2 ^ (expWidth + 1)) (2 ^ expWidthMinus1 - 1)).
                     --- rewrite andb_false_iff; right.
                         rewrite Nat.mod_small.
                         +++ assert (th0: 2 ^ (expWidth + 1) = 4 * 2 ^ expWidthMinus1). {
                               rewrite Nat.pow_add_r with (b := expWidth).
                               rewrite Nat.pow_add_r with (b := expWidthMinus1).
                               clear.
                               simpl.
                               lia.
                             }
                             rewrite <- th0.
                             remember (val2 - 2 ^ (expWidth + 1)) as val3.
                             assert (th01: 2 ^ expWidthMinus1 = 2 ^ expWidthMinus2 * 2) by (rewrite Nat.pow_add_r; auto).
                             rewrite th01 in *.
                             assert (th1: val3 < 2 ^ expWidthMinus2 * 2) by lia.
                             assert (th2: val3 >= 2 ^ expWidthMinus2 * 1) by lia.
                             assert (th3: 2 ^ expWidthMinus2 <> 0) by (clear; pose proof (pow2_zero expWidthMinus2); lia).
                             pose proof (Nat.div_lt_upper_bound _ _ _ th3 th1) as th4.
                             pose proof (Nat.div_le_lower_bound _ _ _ th3 th2) as th5.
                             assert (th6: val3 / 2 ^ expWidthMinus2 = 1) by (clear - th4 th5; lia).
                             rewrite th6; auto.
                         +++ clear - l.
                             rewrite Nat.pow_add_r with (b := expWidth) in l; simpl in l.
                             rewrite Nat.pow_add_r with (b := expWidthMinus1) in l; simpl in l.
                             pose proof (pow2_zero expWidthMinus1); lia.
                     --- assert (sth14: 2 ^ (expWidth + 1) = 2 * 2 ^ expWidth) by
                           (clear; rewrite Nat.pow_add_r; simpl; lia).
                         rewrite <- sth14.
                         remember (val2 - 2 ^ (expWidth + 1)) as val3.
                         assert (th1: val3 < 2 ^ expWidthMinus1 * 2) by lia.
                         assert (th2: val3 >= 2 ^ expWidthMinus1 * 1) by lia.
                         assert (th3: 2 ^ expWidthMinus1 <> 0) by (clear - sth12; lia).
                         pose proof (Nat.div_lt_upper_bound _ _ _ th3 th1) as th4.
                         pose proof (Nat.div_le_lower_bound _ _ _ th3 th2) as th5.
                         assert (th6: val3 / 2 ^ expWidthMinus1 = 1) by (clear - th4 th5; lia).
                         rewrite th6; auto.
                  ** clear - sth7.
                     rewrite ?Nat.pow_add_r in *; simpl in *.
                     pose proof (pow2_zero expWidthMinus2).
                     lia.
               ++ pose proof (pow2_zero expWidthMinus1); lia.
               ++ lia.
               ++ rewrite ?Nat.pow_add_r.
                  rewrite Nat.mul_assoc.
                  auto.
            -- pose proof (pow2_zero expWidthMinus1); lia.
            -- lia.
            -- rewrite Nat.pow_add_r. auto.
          * rewrite Nat.pow_add_r; simpl.
            destruct expWidthMinus2; simpl; try lia.
            pose proof (pow2_zero n0).
            lia.
          * auto.
          * auto.
          * auto.
        + rewrite ?wzero_wplus.
          rewrite ?split1_combine_wplus.
          rewrite andb_false_iff.
          left.
          match goal with
          | |- getBool (weq _ ?P _) && getBool (weq _ ?Q _) = _ =>
            rewrite <- (natToWord_wordToNat _ P);
              rewrite <- (natToWord_wordToNat _ Q)
          end.
          rewrite ?wordToNat_split2.
          rewrite ?wordToNat_wplus, ?wordToNat_combine; simpl.
          rewrite ?Nat.mul_0_r, ?Nat.mul_1_r, ?Nat.add_0_r; simpl.
          rewrite wordToNat_natToWord_idempotent' by
              (rewrite ?Nat.pow_add_r; simpl; pose proof (pow2_zero expWidthMinus2); lia).
          simpl.
          rewrite Nat.mod_small with (b := 2 ^ (expWidth + 1)); simpl.
          * match goal with
              |- context [wordToNat _ (?A)] => remember A as val; simpl in *
            end.
            assert (sth: wordToNat _ val + S (2 ^ expWidthMinus1) < 2 ^ expWidth * 2). {
              pose proof (wordToNat_bound val).
              rewrite ?Nat.pow_add_r with (b := expWidthMinus1) in *; simpl in *.
              pose proof (pow2_zero expWidthMinus1).
              nia.
            }
            pose proof (pow2_zero expWidth) as sth2.
            pose proof (Nat.div_lt_upper_bound _ (2 ^ expWidth) 2 ltac:(lia) sth) as sth3.
            simpl in sth3.
            match type of sth3 with
            | ?P < 2 => case_eq P; intros
            end.
            -- simpl.
               rewrite Nat.div_small_iff in H0 by (pose proof (pow2_zero expWidth); lia).
               rewrite Nat.mod_small by assumption.
               assert (sth4: 2 ^ expWidthMinus1 * 1 <= wordToNat _ val + S (2 ^ expWidthMinus1)) by lia.
               simpl in *.
               pose proof (pow2_zero expWidthMinus1) as sth5.
               pose proof (Nat.div_le_lower_bound _ (2 ^ expWidthMinus1) 1 ltac:(lia) sth4) as sth6.
               assert (sth7:
                         wordToNat _ val + S (2 ^ expWidthMinus1) < 2 ^ expWidthMinus1 * 2) by
                   (rewrite Nat.pow_add_r with (b := expWidthMinus1) in H0; simpl in *; assumption).
               simpl in *.
               pose proof (Nat.div_lt_upper_bound _ (2 ^ expWidthMinus1) 2 ltac:(lia) sth7) as
                   sth8.
               match goal with
               | |- context [(?P + ?Q)/?R] => destruct ((P + Q)/R); simpl; try lia
               end.
               destruct n; auto; lia.
            -- destruct n; [auto|lia].
          * match goal with
            | |- wordToNat _ ?P + _ < _ => pose proof (wordToNat_bound P)
            end.
            rewrite ?Nat.pow_add_r in *; simpl in *.
            pose proof (pow2_zero expWidthMinus2).
            nia.
          * auto.
          * auto.
          * auto.
          * auto.
            Transparent isNaN_or_Inf infOrNaN isZeroFractIn isSpecial normDist subnormFract isZeroExpIn.
    Qed.

    Lemma RawFloat_RecFN_FN_isZero:
      evalExpr (getRawFloat_from_RecFN (getRecFN_from_FN fn))
               (Fin.FS (Fin.FS Fin.F1)) =
      evalExpr (getRawFloat_from_FN fn)
               (Fin.FS (Fin.FS Fin.F1)).
    Proof.
      Opaque isNaN_or_Inf infOrNaN isZeroNaNInf2 isZeroFractIn isSpecial normDist subnormFract adjustedExp isZeroExpIn isZero isZeroRecFN.
      simpl.
      unfold eq_rect_r.
      simpl.
      rewrite isZeroRecFN_isZero.
      auto.
    Qed.
    
    Lemma RawFloat_RecFN_FN_sig:
      evalExpr (getRawFloat_from_RecFN (getRecFN_from_FN fn))
               (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))) =
      evalExpr (getRawFloat_from_FN fn)
               (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))).
    Proof.
      Opaque isNaN_or_Inf infOrNaN isZeroNaNInf2 isZeroFractIn isSpecial normDist subnormFract adjustedExp isZeroExpIn isZero isZeroRecFN.
      simpl.
      reflexivity.
      Transparent isNaN_or_Inf infOrNaN isZeroNaNInf2 isZeroFractIn isSpecial normDist subnormFract adjustedExp isZeroExpIn isZero isZeroRecFN.
    Qed.

    Lemma isSigNaNRawFloat_isSNaN:
      evalExpr (isSigNaNRawFloat (getRawFloat_from_RecFN (getRecFN_from_FN fn))) = evalExpr (isSNaN fn).
    Proof.
      Opaque isNaN_or_Inf infOrNaN isZeroNaNInf2 isZeroFractIn isSpecial normDist subnormFract adjustedExp isZeroExpIn isZero isZeroRecFN.
      simpl.
      rewrite ?split1_combine.
      rewrite isNaN_or_Inf_infOrNaN.
      case_eq (evalExpr (infOrNaN fn)); simpl; intros; auto.
      unfold natToWord; simpl.
      pose proof (infOrNaN_isZeroNaNInf2_1_isZeroFractIn H) as sth.
      simpl in sth.
      assert (sth' : ZToWord 1 1 = natToWord 1 1) by auto. rewrite sth'. clear sth'.
      rewrite sth.
      f_equal.
      case_eq (evalExpr (isZeroExpIn fn)); auto; intros.
      Transparent isNaN_or_Inf infOrNaN isZeroNaNInf2 isZeroFractIn isSpecial normDist subnormFract adjustedExp isZeroExpIn isZero isZeroRecFN.
      exfalso.
      clear sth.
      unfold infOrNaN, isZeroExpIn in *.
      simpl in *.
      match type of H with
      | getBool ?P = true => destruct P; simpl in *; [|discriminate]
      end.
      rewrite e in *.
      apply getBool_weq in H0.
      pose proof (@wzero_wones expWidth ltac:(lia)).
      congruence.
    Qed.

    Lemma bool_prop2 a b c:
      b = negb c ->
      negb (a && b) && negb (a && c) = negb a.
    Proof.
      destruct a, b, c; intros; auto.
    Qed.

    Lemma isFiniteNonzero_simple_complex:
      evalExpr (isFiniteNonzero (getRawFloat_from_RecFN (getRecFN_from_FN fn))) =
      evalExpr (isFiniteNonzero (getRawFloat_from_FN fn)).
    Proof.
      Opaque isNaN_or_Inf infOrNaN isZeroNaNInf2 isZeroFractIn isSpecial normDist subnormFract isZeroExpIn isZeroRecFN isSigNaNRawFloat
             isSigNaNRawFloat_frac isSNaN.
      simpl.
      unfold eq_rect_r.
      simpl.
      rewrite isZeroRecFN_isZero; simpl.
      rewrite isNaN_or_Inf_infOrNaN.
      rewrite isSpecial_infOrNaN.
      rewrite bool_prop2.
      - repeat match goal with
               | |- context[evalExpr ?P] => destruct (evalExpr P); auto
               end.
      - match goal with
        | |- getBool ?P = negb (getBool ?Q) => destruct P, Q; simpl; auto
        end.
        + rewrite e in *.
          discriminate.
        + eapply word1_neq in n; eauto.
          Transparent isNaN_or_Inf infOrNaN isZeroNaNInf2 isZeroFractIn isSpecial normDist subnormFract isZeroExpIn isZeroRecFN isSigNaNRawFloat
                      isSigNaNRawFloat_frac isSNaN.
    Qed.

    Lemma get_exp_from_RecFN_adjustedExp:
      evalExpr (isFiniteNonzero (getRawFloat_from_FN fn)) = true ->
      evalExpr (get_exp_from_RecFN (getRecFN_from_FN fn)) = evalExpr (adjustedExp fn).
    Proof.
      Opaque isNaN_or_Inf infOrNaN isZeroFractIn isSpecial normDist subnormFract isZeroExpIn isZeroRecFN isSigNaNRawFloat
             isSigNaNRawFloat_frac isSNaN.
      simpl.
      intros.
      repeat (rewrite andb_true_iff in *; dest).
      repeat rewrite negb_true_iff in *.
      rewrite !wconcat_w_0.
      rewrite ?split1_combine, ?split2_combine.
      rewrite ?wzero_wplus, ?wor_wzero, ?wzero_wor.
      rewrite isSpecial_infOrNaN in *.
      match type of H0 with
      | ?A && ?B = false => case_eq A; intros sth; rewrite sth in *; simpl in *
      end.
      - rewrite H0 in *; simpl in *.
        rewrite andb_true_r in *.
        rewrite H.
        rewrite ?wor_wzero, ?wzero_wor.
        rewrite ?concat_split'.
        auto. 
      - assert (sth2: evalExpr (infOrNaN fn) = false). {
          match type of H1 with
          | _ && ?P = false => destruct P; auto; simpl in *
          end;
            rewrite andb_true_r in *;
            assumption.
        }
        rewrite sth2 in *; simpl in *.
        rewrite ?wor_wzer, ?wzero_wor.
        rewrite ?concat_split'.
        auto. 
        Transparent isNaN_or_Inf infOrNaN isZeroFractIn isSpecial normDist subnormFract isZeroExpIn isZeroRecFN isSigNaNRawFloat
                    isSigNaNRawFloat_frac isSNaN.
    Qed.

    Lemma RawFloat_RecFN_FN_sExp:
      evalExpr (isFiniteNonzero (getRawFloat_from_RecFN (getRecFN_from_FN fn))) = true ->
      evalExpr (getRawFloat_from_RecFN (getRecFN_from_FN fn)) (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) =
      evalExpr (getRawFloat_from_FN fn) (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))).
    Proof.
      Opaque isNaN_or_Inf infOrNaN isZeroNaNInf2 isZeroFractIn isSpecial normDist subnormFract isZeroExpIn isZeroRecFN isSigNaNRawFloat
             isSigNaNRawFloat_frac isSNaN sExp_expWidth sExp_expWidthMinus1 sExp_expWidthMinus2 isZeroNaNInf1 isZeroNaNInf0 get_exp_from_RecFN adjustedExp.
      rewrite isFiniteNonzero_simple_complex.
      intros.
      simpl;
        rewrite ?split1_combine, ?combine_split.
      eapply get_exp_from_RecFN_adjustedExp; auto.
      Transparent isNaN_or_Inf infOrNaN isZeroNaNInf2 isZeroFractIn isSpecial normDist subnormFract isZeroExpIn isZeroRecFN isSigNaNRawFloat
                  isSigNaNRawFloat_frac isSNaN sExp_expWidth sExp_expWidthMinus1 sExp_expWidthMinus2 isZeroNaNInf1 isZeroNaNInf0 get_exp_from_RecFN adjustedExp.
    Qed.

    Print wltu.

    Lemma isSubnormal_isZeroExpIn_simple:
      evalExpr (isFiniteNonzero (getRawFloat_from_FN fn)) = true ->
      evalExpr (isSubnormal (getRawFloat_from_FN fn)) = evalExpr (isZeroExpIn fn).
    Proof.
      intros finNonZero.
      Opaque isNaN_or_Inf infOrNaN isZeroNaNInf2 isZeroFractIn isSpecial normDist subnormFract isZeroExpIn isZero isZeroRecFN isSigNaNRawFloat
             isSigNaNRawFloat_frac isSNaN get_exp_from_RecFN.
      simpl.
      rewrite wconcat_w_0.
      rewrite wzero_wplus.
      rewrite ?split2_combine.
      simpl.
      unfold natToWord; fold natToWord.
      simpl.
      case_eq (evalExpr (isZeroExpIn fn)); intros sth.
      - rewrite wltu_wordToNat.
        apply Nat.ltb_lt.
        (* match goal with
        | |- getBool ?P = true => destruct P; simpl; auto
        end.
        pre_word_omega. *)
        rewrite ?wordToNat_combine in *; auto; simpl in *; rewrite ?Nat.mul_0_r, ?Nat.mul_1_r, ?Nat.add_0_r in *.
        rewrite wordToNat_wplus in *.
        rewrite ?wordToNat_combine in *; auto; simpl in *; rewrite ?Nat.mul_0_r, ?Nat.mul_1_r, ?Nat.add_0_r in *.
        rewrite wordToNat_wnot in *; simpl in *.
        replace (ZToWord _ 2) with (natToWord expWidthMinus1 2); auto.
        rewrite wordToNat_natToWord_idempotent' in *.
        + assert (sth0: 2 ^ (expWidth + 1) >= wordToNat _ (evalExpr (normDist fn))). {
            pose proof (wordToNat_bound (evalExpr (normDist fn))) as sth2.
            simpl in sth2.
            lia.
          }
          assert (sth1: 2 ^ (expWidth + 1) >= wordToNat _ (evalExpr (normDist fn)) + 1). {
            pose proof (wordToNat_bound (evalExpr (normDist fn))) as sth2.
            simpl in sth2.
            lia.
          }
          assert (sth2: sigWidthMinus1 < 2 ^ (expWidth + 1)). {
            pose proof expWidth_ge_sigWidth.
            do 2 (rewrite Nat.pow_add_r; simpl).
            lia.
          }
          assert (sth3: 2 + 2 ^ expWidthMinus1 >=  wordToNat _ (evalExpr (normDist fn)) + 1). {
            Transparent normDist.
            unfold normDist; simpl.
            match goal with
            | |- context [weq ?w1 ?w2] => destruct (weq w1 w2); simpl; auto
            end.
            rewrite wordToNat_natToWord_idempotent'.
            pose proof expWidth_ge_sigWidth.
            lia.
            lia.
            rewrite evalExpr_countLeadingZeros; simpl.
            match goal with
            | |- _ >= wordToNat _ (countLeadingZerosWord _ _ ?P) + 1 =>
              remember P as val;
                pose proof (countLeadingZerosWord_le_len _ sth2 val); simpl in *
            end.
            rewrite wleu_wordToNat in H. apply Nat.leb_le in H.
            rewrite wordToNat_natToWord_idempotent' in H by assumption.
            assert (sth15: 2 ^ expWidthMinus2 + 4 >= wordToNat _ (countLeadingZerosWord _ (expWidth + 1) val) + 1) by lia.
            assert (sth25: 2 ^ expWidthMinus2 + 4 <= S (S (2 ^ expWidthMinus1))). {
              rewrite Nat.pow_add_r; simpl.
              assert (2 ^ expWidthMinus2 >= 2). {
                destruct expWidthMinus2; try lia.
                destruct n0; try lia.
                simpl.
                pose proof (pow2_zero n0); lia.
              }
              lia.
            }
            lia.
          }
          assert (sth4: 2 ^ (expWidth + 1) - wordToNat _ (evalExpr (normDist fn)) - 1 +
                        (2 + 2 ^ expWidthMinus1)
                        = ((2 + 2 ^ expWidthMinus1) - (wordToNat _ (evalExpr (normDist fn)) + 1)) + 1 * 2 ^ (expWidth + 1)) by lia.
          rewrite sth4 in *.
          rewrite Nat.mod_add by (pose proof (pow2_zero (expWidth + 1)); lia).
          rewrite Nat.mod_small.
          * lia.
          * pose proof (pow2_zero expWidthMinus2).
            rewrite ?Nat.pow_add_r; simpl.
            match goal with
            | |- match ?P with _ => _ end < _ => destruct P; try lia
            end.
            destruct n; try lia.
        + rewrite ?Nat.pow_add_r in *; simpl.
          destruct expWidthMinus2; try lia; simpl.
          pose proof (pow2_zero n); lia.
      - rewrite wconcat_w_0.
        rewrite wltu_wordToNat.
        apply Nat.ltb_nlt.
        (* pre_word_omega. *)
        rewrite wordToNat_combine; auto; simpl in *.
        replace (wordToNat 1 WO~0) with 0; auto.
        rewrite Nat.mul_0_r, Nat.add_0_r in *.
        rewrite wordToNat_wplus in *.
        rewrite ?wordToNat_combine; auto; simpl in *.
        replace (wordToNat 1 WO~0) with 0; auto.
        rewrite Nat.mul_0_r, Nat.mul_1_r, ?Nat.add_0_r in *.
        replace (ZToWord _ 1) with (natToWord expWidthMinus1 1); auto.
        replace (ZToWord _ 2) with (natToWord expWidthMinus1 2); auto.
        rewrite wordToNat_natToWord_idempotent' in * by (rewrite Nat.pow_add_r; simpl; pose proof (pow2_zero expWidthMinus2); lia).
        rewrite ?Nat.mul_0_r, ?Nat.mul_1_r, ?Nat.add_0_r in *.
        rewrite wordToNat_natToWord_idempotent' in *.
        + rewrite Nat.mod_small in *.
          * Transparent isZeroExpIn.
            unfold isZeroExpIn in *; simpl in *.
            match type of sth with
            | getBool ?P = false => destruct P; simpl in *; try discriminate
            end.
            rewrite <- neq0_wneq0 in n.
            lia.
            Opaque isZeroExpIn.
          * match goal with
            | |- wordToNat _ ?a + _ < _ => pose proof (wordToNat_bound a) as sth1
            end.
            rewrite ?Nat.pow_add_r in *; simpl in *.
            pose proof (pow2_zero expWidthMinus2) as sth2.
            clear - sth1 sth2.
            lia.
        + rewrite Nat.pow_add_r; simpl.
          destruct expWidthMinus2; simpl; try lia.
          pose proof pow2_zero n; lia.
      Transparent isNaN_or_Inf infOrNaN isZeroNaNInf2 isZeroFractIn isSpecial normDist subnormFract isZeroExpIn isZero isZeroRecFN isSigNaNRawFloat
             isSigNaNRawFloat_frac isSNaN get_exp_from_RecFN. 
    Qed.
    
    Lemma isSubnormal_isZeroExpIn_complex:
      evalExpr (isFiniteNonzero (getRawFloat_from_RecFN (getRecFN_from_FN fn))) = true ->
      evalExpr (isSubnormal (getRawFloat_from_RecFN (getRecFN_from_FN fn))) = evalExpr (isZeroExpIn fn).
    Proof.
      Opaque isNaN_or_Inf infOrNaN isZeroNaNInf2 isZeroFractIn isSpecial normDist subnormFract isZeroExpIn isZero isZeroRecFN isSigNaNRawFloat
             isSigNaNRawFloat_frac isSNaN get_exp_from_RecFN adjustedExp isFiniteNonzero.
      simpl.
      pose proof isFiniteNonzero_simple_complex as sth0.
      intros sth.
      assert (sth1: evalExpr (isFiniteNonzero (getRawFloat_from_FN fn)) = true) by congruence.
      pose proof (isSubnormal_isZeroExpIn_simple sth1) as sth2.
      unfold eq_rect_r.
      simpl in *.
      
      rewrite get_exp_from_RecFN_adjustedExp by auto.
      auto.
      Transparent isNaN_or_Inf infOrNaN isZeroNaNInf2 isZeroFractIn isSpecial normDist subnormFract isZeroExpIn isZero isZeroRecFN isSigNaNRawFloat
                  isSigNaNRawFloat_frac isSNaN get_exp_from_RecFN adjustedExp isFiniteNonzero.
    Qed.

    Lemma isFiniteNonzero_meaning:
      evalExpr (isFiniteNonzero (getRawFloat_from_RecFN (getRecFN_from_FN fn))) =
      negb (evalExpr (infOrNaN fn)) && negb (evalExpr (isZero fn)).
    Proof.
      Local Opaque isNaN_or_Inf infOrNaN isZeroNaNInf2 isZeroFractIn isSpecial normDist subnormFract isZeroExpIn isZero isZeroRecFN isSigNaNRawFloat
            isSigNaNRawFloat_frac isSNaN.
      simpl.
      unfold eq_rect_r.
      simpl.
      rewrite ?isNaN_or_Inf_infOrNaN.
      rewrite isZeroRecFN_isZero.
      f_equal.
      apply bool_prop2.
      match goal with
      | |- getBool ?P = negb (getBool ?Q) => destruct P, Q; simpl; auto
      end.
      - rewrite e in *; discriminate.
      - eapply word1_neq in n; eauto.
      Transparent isNaN_or_Inf infOrNaN isZeroNaNInf2 isZeroFractIn isSpecial normDist subnormFract isZeroExpIn isZero isZeroRecFN isSigNaNRawFloat
                  isSigNaNRawFloat_frac isSNaN.
    Qed.
        
    Lemma sigWidthMinus1_lt_pow2_expWidth: (sigWidthMinus1 < 2 ^ expWidth).
    Proof.
      rewrite ?Nat.pow_add_r.
      simpl. 
      pose proof (pow2_zero expWidthMinus2) as sth1.
      lia.
    Qed.

    Lemma expWidthMinus2_le_expWidth_plus1:
      2 ^ expWidthMinus2 + 4 < 2 ^ (expWidth + 1).
    Proof.
      clear fn expWidthMinus2_plus4_gt_sigWidth expWidth_prop.
      induction expWidthMinus2; simpl; auto.
      lia.
    Qed.

    Lemma expWidthMinus2_le_expWidth:
      2 ^ expWidthMinus2 + 4 < 2 ^ expWidth.
    Proof.
      clear fn expWidthMinus2_plus4_gt_sigWidth.
      induction expWidthMinus2.
      + inversion expWidth_prop.
      + simpl.
        assert (sth: n = 1 \/ n >= 2) by lia.
        destruct sth as [sth1|sth1]; try rewrite sth1; simpl in *; lia.
    Qed.
        
    Lemma normalizedExp_adjustedExp:
      evalExpr (normalizedExp fn) = evalExpr (adjustedExp fn + $ (2 ^ expWidth))%kami_expr.
    Proof.
      unfold normalizedExp, adjustedExp.
      Opaque isZeroExpIn normDist.
      simpl.
      pose proof (@pow2_lt_2 expWidthMinus1 ltac:(lia)) as sth.
      pose proof (@pow2_lt_2 expWidth ltac:(lia)) as sth1.
      pose proof (pow2_lt_pow2_S expWidthMinus1) as sth2.
      assert (sth3: 2 ^ expWidthMinus1 * 2 = 2 ^ expWidth). {
        rewrite (Nat.add_1_r expWidthMinus1).
        simpl.
        lia.
      }
      pose proof (one_lt_pow2 expWidthMinus2) as sth4.
      match goal with
      | |- context[if ?X then _ else _] => destruct X eqn:Heq
      end.
      + rewrite ?wminus_simple_wminus.
        rewrite ?wzero_wplus. 
        rewrite wneg_wnot.
        rewrite wminus_plus_distr.
        rewrite ?wminus_def.
        do 2 rewrite <- wplus_assoc.
        rewrite wplus_comm.
        do 2 rewrite <- wplus_assoc.
        rewrite wplus_comm.
        rewrite <- ?wplus_assoc.
        apply word_cancel_l.
        apply word_cancel_l.
        rewrite wconcat_w_0.
        rewrite combine_shiftl_plus_n; auto.
        rewrite combine_wplus.
        simpl.
        rewrite ?combine_natToWord_wzero; auto; try lia.
        symmetry.
        rewrite <- wplus_assoc.
        rewrite wplus_comm.
        rewrite <- wplus_assoc.
        apply word_cancel_l.
        rewrite wplus_comm.
        apply move_wplus_wminus'.
        rewrite wminus_def.
        symmetry.
        rewrite wplus_comm.
        apply move_wplus_wminus'.
        rewrite wminus_def.
        rewrite wneg_idempotent.
        rewrite <- natToWord_plus.
        rewrite <- mul2_add.
        rewrite sth3.
        rewrite Nat.add_1_r.
        apply pow2_wneg.
        rewrite ?wordToNat_natToWord_idempotent' by lia.
        apply Nat.lt_add_lt_sub_l.
        rewrite Nat.add_1_r.
        simpl.
        lia.
      + (* rewrite wminus_simple_wminus. *)
        rewrite ?wzero_wplus. 
        rewrite ?wminus_def.
        rewrite <- wplus_assoc.
        apply word_cancel_l.
        rewrite wconcat_w_0.
        rewrite combine_shiftl_plus_n; [| intuition].
        rewrite <- natToWord_plus.
        rewrite combine_natToWord_wzero; [ |lia].
        symmetry.
        apply move_wplus_wminus'.
        rewrite wminus_def.
        rewrite wplus_comm.
        symmetry.
        apply move_wplus_wminus'.
        rewrite wminus_def.
        rewrite wneg_idempotent.
        rewrite <- natToWord_plus.
        replace (2 ^ expWidthMinus1 + 1 + (2 ^ expWidthMinus1 - 1)) with
            (2 ^ expWidthMinus1 + 2 ^ expWidthMinus1) by lia.
        rewrite <- mul2_add.
        rewrite sth3.
        rewrite Nat.add_1_r.
        apply pow2_wneg.
    Qed. 

    Lemma RawFloat_RecFN_FN:
      evalExpr (isFiniteNonzero (getRawFloat_from_RecFN (getRecFN_from_FN fn))) = true ->
      evalExpr (getRawFloat_from_RecFN (getRecFN_from_FN fn)) =
      evalExpr (getRawFloat_from_FN fn).
    Proof.
      intros.
      extensionality x.
      pose proof (mapOrFins_true x) as sth.
      unfold mapOrFins, getFins in *; simpl in sth.
      repeat (destruct sth as [ | sth ]; subst);
      [ apply RawFloat_RecFN_FN_sig
      | apply RawFloat_RecFN_FN_sExp; auto
      | apply RawFloat_RecFN_FN_sign
      | apply RawFloat_RecFN_FN_isZero
      | apply RawFloat_RecFN_FN_isInf
      | apply RawFloat_RecFN_FN_isNaN
      | inversion sth].
    Qed.

    Lemma NF_RawFloat_FN_sExp:
        evalExpr (getNF_from_FN fn) (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) = evalExpr (getNF_from_RawFloat (getRawFloat_from_FN fn))(Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))).
    Proof.
      Opaque normalizedExp adjustedExp.
      simpl.
      unfold eq_rect_r.
      simpl.
      rewrite normalizedExp_adjustedExp. auto.
    Qed.

    Lemma NF_RawFloat_FN:
        evalExpr (getNF_from_FN fn) = evalExpr (getNF_from_RawFloat (getRawFloat_from_FN fn)).
    Proof.
      intros.
      extensionality x.
      pose proof (mapOrFins_true x) as sth.
      unfold mapOrFins, getFins in *; simpl in sth.
      Opaque infOrNaN isSpecial.
      repeat (destruct sth as [ | sth ]; subst);
      [ auto
      | apply NF_RawFloat_FN_sExp
      | auto
      | auto
      | simpl; rewrite isSpecial_infOrNaN; auto
      | simpl; rewrite isSpecial_infOrNaN; auto
      | inversion sth].
      Transparent infOrNaN isSpecial.
    Qed.
    
    Lemma classifyImpl_correct lenMinus10: evalExpr (classify_impl fn lenMinus10) = evalExpr (classify_spec fn lenMinus10).
    Proof.
      pose proof expWidth_ge_sigWidth as expWidth_ge_sigWidth.
      unfold classify_impl, classifyRecFN, classifyRawFloat, classify_spec, ZeroExtend.
      intros.
      cbv [size].
      Opaque isNaN_or_Inf infOrNaN isZeroNaNInf2 isZeroFractIn isSpecial normDist subnormFract adjustedExp isZeroExpIn isZero isZeroRecFN isSigNaNRawFloat
             isSigNaNRawFloat_frac isSNaN isFiniteNonzero isSubnormal.
      repeat (erewrite evalExpr_BinBit; eauto).
      - simpl.
        unfold natToWord; simpl.
        pose proof infOrNaN_isZeroNaNInf2_1_isZeroFractIn as sth.
        simpl in sth.
        rewrite isSigNaNRawFloat_isSNaN.
        rewrite isNaN_or_Inf_infOrNaN.
        case_eq (evalExpr (infOrNaN fn)); intros sth2; simpl; auto.
        specialize (sth sth2).
        assert (sth' : ZToWord 1 1 = natToWord 1 1) by auto; rewrite sth'; clear sth'.
        rewrite sth.
        auto.
      - simpl.
        rewrite isSigNaNRawFloat_isSNaN.
        auto.
      - simpl.
        pose proof infOrNaN_isZeroNaNInf2_0_isZeroFractIn as sth.
        simpl in sth.
        rewrite isNaN_or_Inf_infOrNaN.
        case_eq (evalExpr (infOrNaN fn)); intros sth2; simpl; auto.
        specialize (sth sth2); auto.
        + simpl; rewrite sth.
          rewrite andb_true_r.
          auto.
        + rewrite andb_false_r; simpl.
          auto.
      - simpl.
        apply if_bool_2.
        rewrite <- ?andb_assoc.
        case_eq (evalExpr (isFiniteNonzero (getRawFloat_from_RecFN (getRecFN_from_FN fn)))); simpl; intros sth.
        + pose proof (isSubnormal_isZeroExpIn_complex sth) as sth1.
          simpl in *.
          rewrite isFiniteNonzero_meaning in sth.
          rewrite sth1.
          rewrite andb_true_iff in sth; dest.
          rewrite H; auto.
        + rewrite isFiniteNonzero_meaning in sth.
          f_equal.
          rewrite andb_false_iff in sth; destruct sth; [rewrite H; auto|].
          rewrite negb_false_iff in *.
          Transparent isZero.
          unfold isZero in *.
          simpl in *.
          rewrite andb_true_iff in *; dest.
          rewrite H; simpl.
          rewrite andb_false_r.
          auto.
          Opaque isZero.
      - simpl.
        apply if_bool_2.
        rewrite <- ?andb_assoc.
        f_equal.
        case_eq (evalExpr (isFiniteNonzero (getRawFloat_from_RecFN (getRecFN_from_FN fn)))); simpl; intros sth.
        + pose proof (isSubnormal_isZeroExpIn_complex sth) as sth1.
          simpl in *.
          rewrite isFiniteNonzero_meaning in sth.
          rewrite sth1.
          rewrite andb_true_iff in sth; dest.
          Transparent isZero.
          unfold isZero in *.
          simpl in *.
          rewrite negb_true_iff in *.
          rewrite andb_false_iff in H0; dest.
          destruct H0.
          * rewrite H0; auto.
          * rewrite H0; simpl; auto.
            rewrite andb_true_r.
            auto.
            Opaque isZero.        
        + rewrite isFiniteNonzero_meaning in sth.
          rewrite andb_false_iff in sth; destruct sth.
          * rewrite negb_false_iff in *.
            Transparent infOrNaN isZeroExpIn.
            simpl in *.
            apply getBool_weq in H.
            rewrite H.
            pose proof (@wzero_wones expWidth ltac:(lia)) as sth.
            simpl in *.
            destruct (weq _ (wones expWidth) (natToWord expWidth 0)); simpl; auto.
            rewrite e in *.
            tauto.
            Opaque infOrNaN isZeroExpIn.
          * Transparent isZero.
            simpl in *.
            rewrite negb_false_iff in H; dest.
            rewrite andb_true_iff in H; dest.
            rewrite H, H0 in *; simpl; auto.
            Opaque isZero.
      - simpl.
        unfold eq_rect_r.
        simpl.
        rewrite isZeroRecFN_isZero.
        Transparent isZero.
        unfold isZero.
        Opaque isZero.
        simpl.
        rewrite andb_assoc.
        auto.
      - simpl.
        unfold eq_rect_r.
        simpl.
        rewrite isZeroRecFN_isZero.
        Transparent isZero.
        unfold isZero.
        Opaque isZero.
        simpl.
        rewrite andb_assoc.
        auto.
      - simpl.
        apply if_bool_2.
        rewrite <- ?andb_assoc.
        f_equal.
        case_eq (evalExpr (isFiniteNonzero (getRawFloat_from_RecFN (getRecFN_from_FN fn)))); simpl; intros sth.
        + pose proof (isSubnormal_isZeroExpIn_complex sth) as sth1.
          simpl in *.
          rewrite isFiniteNonzero_meaning in sth.
          rewrite sth1.
          rewrite andb_true_iff in sth; dest.
          Transparent isZero.
          unfold isZero in *.
          simpl in *.
          rewrite negb_true_iff in *.
          rewrite andb_false_iff in H0; dest.
          destruct H0.
          * rewrite H0; auto.
          * rewrite H0; simpl; auto.
            rewrite andb_true_r.
            auto.
            Opaque isZero.        
        + rewrite isFiniteNonzero_meaning in sth.
          rewrite andb_false_iff in sth; destruct sth.
          * rewrite negb_false_iff in *.
            Transparent infOrNaN isZeroExpIn.
            simpl in *.
            apply getBool_weq in H.
            rewrite H.
            pose proof (@wzero_wones expWidth ltac:(lia)) as sth.
            simpl in *.
            destruct (weq _ (wones expWidth) (natToWord expWidth 0)); simpl; auto.
            rewrite e in *.
            tauto.
            Opaque infOrNaN isZeroExpIn.
          * Transparent isZero.
            simpl in *.
            rewrite negb_false_iff in H; dest.
            rewrite andb_true_iff in H; dest.
            rewrite H, H0 in *; simpl; auto.
            Opaque isZero.
      - simpl.
        apply if_bool_2.
        rewrite <- ?andb_assoc.
        case_eq (evalExpr (isFiniteNonzero (getRawFloat_from_RecFN (getRecFN_from_FN fn)))); simpl; intros sth.
        + pose proof (isSubnormal_isZeroExpIn_complex sth) as sth1.
          simpl in *.
          rewrite isFiniteNonzero_meaning in sth.
          rewrite sth1.
          rewrite andb_true_iff in sth; dest.
          rewrite H; auto.
        + rewrite isFiniteNonzero_meaning in sth.
          f_equal.
          rewrite andb_false_iff in sth; destruct sth; [rewrite H; auto|].
          rewrite negb_false_iff in *.
          Transparent isZero.
          unfold isZero in *.
          simpl in *.
          rewrite andb_true_iff in *; dest.
          rewrite H; simpl.
          rewrite andb_false_r.
          auto.
          Opaque isZero.
      - simpl.
        rewrite isNaN_or_Inf_infOrNaN.
        unfold natToWord.
        simpl.
        pose proof infOrNaN_isZeroNaNInf2_0_isZeroFractIn as sth.
        simpl in sth.
        case_eq (evalExpr (infOrNaN fn)); intros sth2; simpl; auto.
        + specialize (sth sth2); auto.
          replace (ZToWord 1 0) with (natToWord 1 0); auto.
          rewrite sth.
          rewrite andb_true_r.
          auto.
        + rewrite andb_false_r; simpl.
          auto.
          Transparent isNaN_or_Inf infOrNaN isZeroNaNInf2 isZeroFractIn isSpecial normDist subnormFract adjustedExp isZeroExpIn isZero isZeroRecFN isSigNaNRawFloat
                      isSigNaNRawFloat_frac isSNaN isFiniteNonzero isSubnormal.
    Qed.
  End FN.

  Inductive emptyRegsRel: RegsT -> RegsT -> Prop :=
  | emptyRegsConst: emptyRegsRel nil nil.

  Theorem ClassifyCorrect lenMinus10:
    TraceInclusion (Base (ClassifyImpl "impl" expWidthMinus2 sigWidthMinus2 lenMinus10))
                   (Base (ClassifySpec "spec" expWidthMinus2 sigWidthMinus2 lenMinus10)).
  Proof.
    eapply simulationZero with (simRel := emptyRegsRel); try solve [constructor]; intros.
    - exists nil.
      inv H.
      split; try constructor; auto.
    - inv H; simpl in *; [| discriminate].
      destruct HInRules; [| tauto].
      inv H.
      inv HLabel.
      repeat match goal with
             | H: SemAction _ _ _ _ _ _ |- _ => 
               apply inversionSemAction in H; dest
             end; subst.
      right.
      exists nil, "spec#classify", nil.
      split.
      + econstructor 2.
        * simpl.
          inv H1.
          auto.
        * simpl.
          left; reflexivity.
        * repeat econstructor; unfold key_not_In; intros; intro.
        * simpl; intros; tauto.
        * simpl; intros; tauto.
        * do 8 f_equal; intros. 
          eapply  classifyImpl_correct.
        * intros.
          rewrite DisjKeyWeak_same by (apply string_dec).
          unfold DisjKeyWeak; intros.
          simpl in *.
          auto.
        * intros.
          simpl in *.
          tauto.
        * inv H1; simpl in *.
          econstructor; eauto.
      + split.
        * inv H1.
          unfold UpdRegs.
          split; auto.
        * inv H1.
          unfold UpdRegs in H0.
          dest.
          simpl in H0.
          apply eq_sym in H0.
          apply map_eq_nil in H0; subst.
          constructor.
  Qed.
End Properties.
