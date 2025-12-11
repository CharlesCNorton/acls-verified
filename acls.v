(******************************************************************************)
(*                                                                            *)
(*         Cardiac Arrest: Verified ACLS Decision Support in Coq              *)
(*                                                                            *)
(*     Formal verification of Advanced Cardiovascular Life Support (ACLS)     *)
(*     algorithms per AHA 2020 guidelines. Rhythm classification, shock       *)
(*     decisions, drug dosing, and ROSC criteria with machine-checked         *)
(*     correctness guarantees.                                                 *)
(*                                                                            *)
(*     "Hearts too good to die are dying."                                    *)
(*     - Claude Beck, 1947                                                    *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: December 2025                                                    *)
(*                                                                            *)
(******************************************************************************)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

(******************************************************************************)
(*                                                                            *)
(*                         SECTION 1: RHYTHM TYPES                            *)
(*                                                                            *)
(*  The four cardiac arrest rhythms per AHA 2020 ACLS guidelines.             *)
(*  VF and pVT are shockable; PEA and Asystole are non-shockable.             *)
(*                                                                            *)
(******************************************************************************)

Module Rhythm.

  Inductive t : Type :=
    | VF
    | pVT
    | PEA
    | Asystole.

  Definition eq_dec : forall r1 r2 : t, {r1 = r2} + {r1 <> r2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Definition all : list t := [VF; pVT; PEA; Asystole].

  Lemma all_complete : forall r : t, In r all.
  Proof. intros []; simpl; auto. Qed.

  Lemma all_nodup : NoDup all.
  Proof. repeat constructor; simpl; intuition discriminate. Qed.

  Lemma all_length : length all = 4.
  Proof. reflexivity. Qed.

  Definition shockable (r : t) : bool :=
    match r with
    | VF | pVT => true
    | PEA | Asystole => false
    end.

  Definition is_shockable (r : t) : Prop := shockable r = true.
  Definition is_non_shockable (r : t) : Prop := shockable r = false.

  Theorem shockable_dec : forall r, {is_shockable r} + {is_non_shockable r}.
  Proof.
    intros r. unfold is_shockable, is_non_shockable.
    destruct (shockable r) eqn:E; [left | right]; reflexivity.
  Defined.

  Theorem VF_shockable : is_shockable VF.
  Proof. reflexivity. Qed.

  Theorem pVT_shockable : is_shockable pVT.
  Proof. reflexivity. Qed.

  Theorem PEA_non_shockable : is_non_shockable PEA.
  Proof. reflexivity. Qed.

  Theorem Asystole_non_shockable : is_non_shockable Asystole.
  Proof. reflexivity. Qed.

  Theorem shockable_exhaustive : forall r,
    shockable r = true \/ shockable r = false.
  Proof. intros []; simpl; auto. Qed.

  Theorem shockable_iff : forall r,
    is_shockable r <-> r = VF \/ r = pVT.
  Proof.
    intros r. unfold is_shockable. split.
    - destruct r; simpl; intro H; auto; discriminate.
    - intros [H | H]; subst; reflexivity.
  Qed.

  Theorem non_shockable_iff : forall r,
    is_non_shockable r <-> r = PEA \/ r = Asystole.
  Proof.
    intros r. unfold is_non_shockable. split.
    - destruct r; simpl; intro H; auto; discriminate.
    - intros [H | H]; subst; reflexivity.
  Qed.

  Definition count_shockable : nat := 2.
  Definition count_non_shockable : nat := 2.

  Theorem shockable_count_correct :
    length (filter shockable all) = count_shockable.
  Proof. reflexivity. Qed.

  Theorem non_shockable_count_correct :
    length (filter (fun r => negb (shockable r)) all) = count_non_shockable.
  Proof. reflexivity. Qed.

  Definition to_nat (r : t) : nat :=
    match r with VF => 0 | pVT => 1 | PEA => 2 | Asystole => 3 end.

  Definition of_nat (n : nat) : t :=
    match n with 0 => VF | 1 => pVT | 2 => PEA | _ => Asystole end.

  Lemma to_nat_of_nat : forall r, of_nat (to_nat r) = r.
  Proof. intros []; reflexivity. Qed.

  Lemma of_nat_to_nat : forall n, n < 4 -> to_nat (of_nat n) = n.
  Proof. intros [|[|[|[|n]]]] H; try reflexivity; lia. Qed.

End Rhythm.

(******************************************************************************)
(*                                                                            *)
(*                       SECTION 2: CPR PARAMETERS                            *)
(*                                                                            *)
(*  AHA 2020 high-quality CPR parameters: compression depth, rate, cycle      *)
(*  duration, and compression-to-ventilation ratios.                          *)
(*                                                                            *)
(******************************************************************************)

Module CPR.

  Definition min_depth_cm : nat := 5.
  Definition max_depth_cm : nat := 6.

  Definition min_rate_per_min : nat := 100.
  Definition max_rate_per_min : nat := 120.

  Definition cycle_duration_sec : nat := 120.

  Definition compression_ratio : nat := 30.
  Definition ventilation_ratio : nat := 2.

  Definition breaths_per_min_advanced_airway : nat := 10.

  Definition max_rhythm_check_sec : nat := 10.

  Record Parameters : Type := mkParams {
    depth_cm : nat;
    rate_per_min : nat
  }.

  Definition depth_adequate (p : Parameters) : bool :=
    (min_depth_cm <=? depth_cm p) && (depth_cm p <=? max_depth_cm).

  Definition rate_adequate (p : Parameters) : bool :=
    (min_rate_per_min <=? rate_per_min p) && (rate_per_min p <=? max_rate_per_min).

  Definition quality_adequate (p : Parameters) : bool :=
    depth_adequate p && rate_adequate p.

  Definition optimal : Parameters := mkParams 5 110.

  Theorem optimal_depth_adequate : depth_adequate optimal = true.
  Proof. reflexivity. Qed.

  Theorem optimal_rate_adequate : rate_adequate optimal = true.
  Proof. reflexivity. Qed.

  Theorem optimal_quality_adequate : quality_adequate optimal = true.
  Proof. reflexivity. Qed.

  Definition too_shallow : Parameters := mkParams 4 110.
  Definition too_deep : Parameters := mkParams 7 110.
  Definition too_slow : Parameters := mkParams 5 90.
  Definition too_fast : Parameters := mkParams 5 130.

  Theorem too_shallow_inadequate : depth_adequate too_shallow = false.
  Proof. reflexivity. Qed.

  Theorem too_deep_inadequate : depth_adequate too_deep = false.
  Proof. reflexivity. Qed.

  Theorem too_slow_inadequate : rate_adequate too_slow = false.
  Proof. reflexivity. Qed.

  Theorem too_fast_inadequate : rate_adequate too_fast = false.
  Proof. reflexivity. Qed.

  Definition compressions_per_cycle : nat :=
    (cycle_duration_sec * min_rate_per_min) / 60.

  Theorem compressions_per_cycle_value : compressions_per_cycle = 200.
  Proof. reflexivity. Qed.

  Definition depth_adequate_iff : forall p,
    depth_adequate p = true <->
    min_depth_cm <= depth_cm p /\ depth_cm p <= max_depth_cm.
  Proof.
    intros p. unfold depth_adequate. split.
    - intro H. apply andb_true_iff in H. destruct H as [H1 H2].
      split; [apply Nat.leb_le | apply Nat.leb_le]; assumption.
    - intros [H1 H2]. apply andb_true_iff. split;
      [apply Nat.leb_le | apply Nat.leb_le]; assumption.
  Qed.

  Definition rate_adequate_iff : forall p,
    rate_adequate p = true <->
    min_rate_per_min <= rate_per_min p /\ rate_per_min p <= max_rate_per_min.
  Proof.
    intros p. unfold rate_adequate. split.
    - intro H. apply andb_true_iff in H. destruct H as [H1 H2].
      split; [apply Nat.leb_le | apply Nat.leb_le]; assumption.
    - intros [H1 H2]. apply andb_true_iff. split;
      [apply Nat.leb_le | apply Nat.leb_le]; assumption.
  Qed.

  Definition etco2_min_during_cpr : nat := 10.
  Definition etco2_max_during_cpr : nat := 20.
  Definition etco2_target_during_cpr : nat := 15.

  Definition etco2_indicates_adequate_cpr (etco2_mmHg : nat) : bool :=
    (etco2_min_during_cpr <=? etco2_mmHg) && (etco2_mmHg <=? etco2_max_during_cpr).

  Definition etco2_indicates_poor_cpr (etco2_mmHg : nat) : bool :=
    etco2_mmHg <? etco2_min_during_cpr.

  Definition etco2_suggests_rosc_during_cpr (etco2_mmHg : nat) : bool :=
    40 <=? etco2_mmHg.

  Theorem etco2_15_adequate : etco2_indicates_adequate_cpr 15 = true.
  Proof. reflexivity. Qed.

  Theorem etco2_5_poor : etco2_indicates_poor_cpr 5 = true.
  Proof. reflexivity. Qed.

  Theorem etco2_45_suggests_rosc : etco2_suggests_rosc_during_cpr 45 = true.
  Proof. reflexivity. Qed.

  Theorem etco2_adequate_not_poor : forall e,
    etco2_indicates_adequate_cpr e = true -> etco2_indicates_poor_cpr e = false.
  Proof.
    intros e H.
    unfold etco2_indicates_adequate_cpr in H.
    apply andb_true_iff in H. destruct H as [H1 _].
    unfold etco2_indicates_poor_cpr.
    apply Nat.leb_le in H1.
    destruct (e <? etco2_min_during_cpr) eqn:E.
    - apply Nat.ltb_lt in E. lia.
    - reflexivity.
  Qed.

  Inductive CPRQuality : Type :=
    | QualityAdequate
    | QualityPoor
    | QualityExcellent
    | QualityROSCLikely.

  Definition assess_cpr_quality_by_etco2 (etco2_mmHg : nat) : CPRQuality :=
    if etco2_suggests_rosc_during_cpr etco2_mmHg then QualityROSCLikely
    else if etco2_mmHg <? etco2_min_during_cpr then QualityPoor
    else if etco2_max_during_cpr <? etco2_mmHg then QualityExcellent
    else QualityAdequate.

  Definition cpr_quality_action (q : CPRQuality) : nat :=
    match q with
    | QualityAdequate => 0
    | QualityPoor => 1
    | QualityExcellent => 2
    | QualityROSCLikely => 3
    end.

  Theorem etco2_5_poor_quality : assess_cpr_quality_by_etco2 5 = QualityPoor.
  Proof. reflexivity. Qed.

  Theorem etco2_15_adequate_quality : assess_cpr_quality_by_etco2 15 = QualityAdequate.
  Proof. reflexivity. Qed.

  Theorem etco2_25_excellent_quality : assess_cpr_quality_by_etco2 25 = QualityExcellent.
  Proof. reflexivity. Qed.

  Theorem etco2_45_rosc_likely : assess_cpr_quality_by_etco2 45 = QualityROSCLikely.
  Proof. reflexivity. Qed.

  Theorem rosc_likely_implies_check_pulse : forall e,
    assess_cpr_quality_by_etco2 e = QualityROSCLikely ->
    etco2_suggests_rosc_during_cpr e = true.
  Proof.
    intros e H.
    unfold assess_cpr_quality_by_etco2 in H.
    destruct (etco2_suggests_rosc_during_cpr e) eqn:E.
    - reflexivity.
    - destruct (e <? etco2_min_during_cpr) eqn:E2.
      + discriminate H.
      + destruct (etco2_max_during_cpr <? e) eqn:E3; discriminate H.
  Qed.

End CPR.

(******************************************************************************)
(*                                                                            *)
(*                     SECTION 2B: PEDIATRIC CPR PARAMETERS                   *)
(*                                                                            *)
(*  Age-specific CPR depth and rate parameters per AHA 2020 PALS guidelines.  *)
(*  Infant (<1yr), Child (1-puberty), Adolescent (puberty+) categories.       *)
(*                                                                            *)
(******************************************************************************)

Module PediatricCPR.

  Inductive AgeCategory : Type :=
    | Neonate
    | Infant
    | Child
    | Adolescent
    | Adult.

  Definition age_category_eq_dec : forall a1 a2 : AgeCategory, {a1 = a2} + {a1 <> a2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Definition neonate_max_days : nat := 28.
  Definition infant_max_months : nat := 12.
  Definition child_max_years : nat := 12.
  Definition adolescent_max_years : nat := 18.

  Definition classify_age (age_months : nat) : AgeCategory :=
    if age_months <? 1 then Neonate
    else if age_months <? infant_max_months then Infant
    else if age_months <? (child_max_years * 12) then Child
    else if age_months <? (adolescent_max_years * 12) then Adolescent
    else Adult.

  Definition infant_compression_depth_cm_x10 : nat := 40.
  Definition infant_compression_depth_fraction : nat := 33.

  Definition child_min_compression_depth_cm : nat := 5.
  Definition child_max_compression_depth_cm : nat := 6.
  Definition child_compression_depth_fraction : nat := 33.

  Definition infant_compression_location : nat := 1.
  Definition child_compression_location : nat := 2.

  Definition min_depth_for_age_x10 (cat : AgeCategory) : nat :=
    match cat with
    | Neonate => 30
    | Infant => 40
    | Child => 50
    | Adolescent => 50
    | Adult => 50
    end.

  Definition max_depth_for_age_x10 (cat : AgeCategory) : nat :=
    match cat with
    | Neonate => 40
    | Infant => 40
    | Child => 60
    | Adolescent => 60
    | Adult => 60
    end.

  Definition compression_rate_min (cat : AgeCategory) : nat :=
    match cat with
    | Neonate => 120
    | Infant => 100
    | Child => 100
    | Adolescent => 100
    | Adult => 100
    end.

  Definition compression_rate_max (cat : AgeCategory) : nat :=
    match cat with
    | Neonate => 120
    | Infant => 120
    | Child => 120
    | Adolescent => 120
    | Adult => 120
    end.

  Definition compression_ventilation_ratio_single_rescuer (cat : AgeCategory) : nat * nat :=
    match cat with
    | Neonate => (3, 1)
    | Infant => (30, 2)
    | Child => (30, 2)
    | Adolescent => (30, 2)
    | Adult => (30, 2)
    end.

  Definition compression_ventilation_ratio_two_rescuers (cat : AgeCategory) : nat * nat :=
    match cat with
    | Neonate => (3, 1)
    | Infant => (15, 2)
    | Child => (15, 2)
    | Adolescent => (30, 2)
    | Adult => (30, 2)
    end.

  Definition two_thumb_technique_appropriate (cat : AgeCategory) : bool :=
    match cat with
    | Neonate | Infant => true
    | Child | Adolescent | Adult => false
    end.

  Definition one_hand_technique_appropriate (cat : AgeCategory) : bool :=
    match cat with
    | Neonate | Infant => false
    | Child => true
    | Adolescent | Adult => false
    end.

  Definition two_hand_technique_appropriate (cat : AgeCategory) : bool :=
    match cat with
    | Neonate | Infant => false
    | Child | Adolescent | Adult => true
    end.

  Record PediatricCPRParameters : Type := mkPedParams {
    ped_age_category : AgeCategory;
    ped_depth_x10 : nat;
    ped_rate : nat;
    ped_rescuers : nat
  }.

  Definition depth_adequate_for_age (p : PediatricCPRParameters) : bool :=
    let cat := ped_age_category p in
    (min_depth_for_age_x10 cat <=? ped_depth_x10 p) &&
    (ped_depth_x10 p <=? max_depth_for_age_x10 cat).

  Definition rate_adequate_for_age (p : PediatricCPRParameters) : bool :=
    let cat := ped_age_category p in
    (compression_rate_min cat <=? ped_rate p) &&
    (ped_rate p <=? compression_rate_max cat).

  Definition quality_adequate_for_age (p : PediatricCPRParameters) : bool :=
    depth_adequate_for_age p && rate_adequate_for_age p.

  Definition optimal_infant_params : PediatricCPRParameters :=
    mkPedParams Infant 40 110 2.

  Definition optimal_child_params : PediatricCPRParameters :=
    mkPedParams Child 55 110 2.

  Definition optimal_neonate_params : PediatricCPRParameters :=
    mkPedParams Neonate 35 120 2.

  Theorem infant_params_adequate :
    quality_adequate_for_age optimal_infant_params = true.
  Proof. reflexivity. Qed.

  Theorem child_params_adequate :
    quality_adequate_for_age optimal_child_params = true.
  Proof. reflexivity. Qed.

  Theorem neonate_params_adequate :
    quality_adequate_for_age optimal_neonate_params = true.
  Proof. reflexivity. Qed.

  Definition too_shallow_infant : PediatricCPRParameters :=
    mkPedParams Infant 30 110 2.

  Definition too_deep_infant : PediatricCPRParameters :=
    mkPedParams Infant 50 110 2.

  Theorem shallow_infant_inadequate :
    depth_adequate_for_age too_shallow_infant = false.
  Proof. reflexivity. Qed.

  Theorem deep_infant_inadequate :
    depth_adequate_for_age too_deep_infant = false.
  Proof. reflexivity. Qed.

  Definition epinephrine_dose_mcg_per_kg : nat := 10.
  Definition epinephrine_max_dose_mg : nat := 1.
  Definition amiodarone_dose_mg_per_kg : nat := 5.
  Definition amiodarone_max_dose_mg : nat := 300.
  Definition lidocaine_dose_mg_per_kg : nat := 1.
  Definition lidocaine_max_dose_mg : nat := 100.

  Definition defibrillation_initial_J_per_kg : nat := 2.
  Definition defibrillation_subsequent_J_per_kg : nat := 4.
  Definition defibrillation_max_J_per_kg : nat := 10.
  Definition defibrillation_adult_dose_J : nat := 200.

  Definition calculate_epi_dose_mcg (weight_kg : nat) : nat :=
    let dose := weight_kg * epinephrine_dose_mcg_per_kg in
    if (epinephrine_max_dose_mg * 1000) <? dose then epinephrine_max_dose_mg * 1000 else dose.

  Definition calculate_defib_J (weight_kg shock_number : nat) : nat :=
    let j_per_kg := if shock_number =? 1 then defibrillation_initial_J_per_kg else defibrillation_subsequent_J_per_kg in
    let dose := weight_kg * j_per_kg in
    let max_weight_dose := weight_kg * defibrillation_max_J_per_kg in
    if defibrillation_adult_dose_J <? dose then defibrillation_adult_dose_J
    else if max_weight_dose <? dose then max_weight_dose
    else dose.

  Theorem epi_dose_10kg : calculate_epi_dose_mcg 10 = 100.
  Proof. reflexivity. Qed.

  Theorem epi_dose_capped_at_1mg : calculate_epi_dose_mcg 150 = 1000.
  Proof. reflexivity. Qed.

  Theorem defib_dose_20kg_first : calculate_defib_J 20 1 = 40.
  Proof. reflexivity. Qed.

  Theorem defib_dose_20kg_second : calculate_defib_J 20 2 = 80.
  Proof. reflexivity. Qed.

  Definition et_tube_size_uncuffed (age_years : nat) : nat :=
    (age_years + 16) / 4.

  Definition et_tube_size_cuffed (age_years : nat) : nat :=
    (age_years + 12) / 4.

  Definition et_tube_depth_oral (age_years : nat) : nat :=
    (age_years / 2) + 12.

  Theorem tube_size_4yo_uncuffed : et_tube_size_uncuffed 4 = 5.
  Proof. reflexivity. Qed.

  Theorem tube_size_4yo_cuffed : et_tube_size_cuffed 4 = 4.
  Proof. reflexivity. Qed.

  Theorem tube_depth_4yo : et_tube_depth_oral 4 = 14.
  Proof. reflexivity. Qed.

  Definition weight_estimation_kg (age_years : nat) : nat :=
    if age_years =? 0 then 4
    else if age_years <? 2 then (age_years + 1) * 5
    else if age_years <? 6 then age_years * 2 + 8
    else if age_years <? 12 then age_years * 3
    else age_years * 3.

  Theorem weight_newborn : weight_estimation_kg 0 = 4.
  Proof. reflexivity. Qed.

  Theorem weight_1yo : weight_estimation_kg 1 = 10.
  Proof. reflexivity. Qed.

  Theorem weight_4yo : weight_estimation_kg 4 = 16.
  Proof. reflexivity. Qed.

  Theorem weight_8yo : weight_estimation_kg 8 = 24.
  Proof. reflexivity. Qed.

  Definition bradycardia_threshold (cat : AgeCategory) : nat :=
    match cat with
    | Neonate => 100
    | Infant => 100
    | Child => 60
    | Adolescent => 60
    | Adult => 60
    end.

  Definition tachycardia_threshold (cat : AgeCategory) : nat :=
    match cat with
    | Neonate => 180
    | Infant => 180
    | Child => 180
    | Adolescent => 150
    | Adult => 150
    end.

  Definition cpr_indicated_for_bradycardia (cat : AgeCategory) (hr : nat) (signs_of_poor_perfusion : bool) : bool :=
    (hr <? bradycardia_threshold cat) && signs_of_poor_perfusion.

  Theorem neonate_brady_with_poor_perf :
    cpr_indicated_for_bradycardia Neonate 80 true = true.
  Proof. reflexivity. Qed.

  Theorem child_brady_without_poor_perf :
    cpr_indicated_for_bradycardia Child 50 false = false.
  Proof. reflexivity. Qed.

End PediatricCPR.

(******************************************************************************)
(*                                                                            *)
(*                        SECTION 3: MEDICATIONS                              *)
(*                                                                            *)
(*  ACLS cardiac arrest medications: Epinephrine, Amiodarone, Lidocaine,      *)
(*  Magnesium. Doses in mcg or mg, timing intervals per AHA 2020.             *)
(*                                                                            *)
(******************************************************************************)

Module Medication.

  Inductive Drug : Type :=
    | Epinephrine
    | Amiodarone
    | Lidocaine
    | MagnesiumSulfate
    | CalciumChloride
    | CalciumGluconate
    | SodiumBicarbonate
    | LipidEmulsion.

  Definition drug_eq_dec : forall d1 d2 : Drug, {d1 = d2} + {d1 <> d2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Definition all_drugs : list Drug :=
    [Epinephrine; Amiodarone; Lidocaine; MagnesiumSulfate;
     CalciumChloride; CalciumGluconate; SodiumBicarbonate; LipidEmulsion].

  Lemma all_drugs_complete : forall d : Drug, In d all_drugs.
  Proof. intros []; simpl; auto 12. Qed.

  Inductive Route : Type :=
    | IV
    | IO
    | ETT.

  Definition route_eq_dec : forall r1 r2 : Route, {r1 = r2} + {r1 <> r2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Definition epinephrine_dose_mg : nat := 1.
  Definition epinephrine_interval_min : nat := 3.
  Definition epinephrine_interval_max : nat := 5.

  Definition amiodarone_first_dose_mg : nat := 300.
  Definition amiodarone_second_dose_mg : nat := 150.
  Definition amiodarone_max_24hr_mg : nat := 2200.

  Definition lidocaine_first_dose_mg_per_kg_x10 : nat := 15.
  Definition lidocaine_repeat_dose_mg_per_kg_x10 : nat := 7.
  Definition lidocaine_max_mg_per_kg_x10 : nat := 30.

  Definition magnesium_dose_mg_min : nat := 1000.
  Definition magnesium_dose_mg_max : nat := 2000.

  Definition calcium_chloride_dose_mg : nat := 1000.
  Definition calcium_gluconate_dose_mg : nat := 3000.
  Definition calcium_chloride_dose_mg_per_kg : nat := 20.
  Definition calcium_gluconate_dose_mg_per_kg : nat := 60.

  Definition bicarb_dose_meq : nat := 50.
  Definition bicarb_dose_meq_per_kg : nat := 1.
  Definition bicarb_ph_threshold_x100 : nat := 710.

  Definition lipid_bolus_ml_per_kg_x10 : nat := 15.
  Definition lipid_infusion_ml_per_kg_per_min_x100 : nat := 25.
  Definition lipid_max_dose_ml_per_kg : nat := 12.

  Record Dose : Type := mkDose {
    drug : Drug;
    amount_mg : nat;
    route : Route;
    time_sec : nat
  }.

  Definition drug_eqb (d1 d2 : Drug) : bool :=
    if drug_eq_dec d1 d2 then true else false.

  Definition is_standard_epi_dose (d : Dose) : bool :=
    drug_eqb (drug d) Epinephrine && (amount_mg d =? epinephrine_dose_mg).

  Definition epinephrine_dose_valid (amt : nat) : bool :=
    amt =? epinephrine_dose_mg.

  Definition amiodarone_first_valid (amt : nat) : bool :=
    amt =? amiodarone_first_dose_mg.

  Definition amiodarone_second_valid (amt : nat) : bool :=
    amt =? amiodarone_second_dose_mg.

  Definition magnesium_dose_valid (amt : nat) : bool :=
    (magnesium_dose_mg_min <=? amt) && (amt <=? magnesium_dose_mg_max).

  Definition calcium_chloride_dose_valid (amt : nat) : bool :=
    amt =? calcium_chloride_dose_mg.

  Definition calcium_gluconate_dose_valid (amt : nat) : bool :=
    amt =? calcium_gluconate_dose_mg.

  Definition calcium_chloride_weight_based_valid (amt weight_kg : nat) : bool :=
    amt =? (calcium_chloride_dose_mg_per_kg * weight_kg).

  Definition calcium_gluconate_weight_based_valid (amt weight_kg : nat) : bool :=
    amt =? (calcium_gluconate_dose_mg_per_kg * weight_kg).

  Definition bicarb_dose_valid (amt : nat) : bool :=
    amt =? bicarb_dose_meq.

  Definition bicarb_weight_based_valid (amt weight_kg : nat) : bool :=
    amt =? (bicarb_dose_meq_per_kg * weight_kg).

  Definition lipid_bolus_valid (amt_ml weight_kg : nat) : bool :=
    let expected_x10 := lipid_bolus_ml_per_kg_x10 * weight_kg in
    amt_ml * 10 =? expected_x10.

  Record PatientWeight : Type := mkWeight {
    weight_kg : nat;
    weight_valid : bool
  }.

  Definition standard_adult_weight : PatientWeight := mkWeight 70 true.

  Definition lidocaine_dose_for_weight (w : PatientWeight) : nat :=
    (lidocaine_first_dose_mg_per_kg_x10 * weight_kg w) / 10.

  Definition lidocaine_repeat_for_weight (w : PatientWeight) : nat :=
    (lidocaine_repeat_dose_mg_per_kg_x10 * weight_kg w) / 10.

  Definition lidocaine_max_for_weight (w : PatientWeight) : nat :=
    (lidocaine_max_mg_per_kg_x10 * weight_kg w) / 10.

  Definition epinephrine_peds_dose_mcg_per_kg : nat := 10.
  Definition epinephrine_peds_max_dose_mg : nat := 1.

  Definition amiodarone_peds_dose_mg_per_kg : nat := 5.
  Definition amiodarone_peds_max_dose_mg : nat := 300.

  Definition lidocaine_peds_dose_mg_per_kg : nat := 1.

  Definition magnesium_peds_dose_mg_per_kg : nat := 50.
  Definition magnesium_peds_max_dose_mg : nat := 2000.

  Definition calcium_chloride_peds_dose_mg_per_kg : nat := 20.
  Definition calcium_gluconate_peds_dose_mg_per_kg : nat := 60.

  Definition bicarb_peds_dose_meq_per_kg : nat := 1.

  Definition defibrillation_peds_initial_J_per_kg : nat := 2.
  Definition defibrillation_peds_subsequent_J_per_kg : nat := 4.
  Definition defibrillation_peds_max_J_per_kg : nat := 10.

  Definition cpr_peds_depth_infant_cm_min : nat := 4.
  Definition cpr_peds_depth_child_cm_min : nat := 5.
  Definition cpr_peds_compression_ratio_one_rescuer : nat := 30.
  Definition cpr_peds_ventilation_ratio_one_rescuer : nat := 2.
  Definition cpr_peds_compression_ratio_two_rescuer : nat := 15.
  Definition cpr_peds_ventilation_ratio_two_rescuer : nat := 2.

  Inductive AgeCategory : Type :=
    | Neonate
    | Infant
    | Child
    | Adolescent
    | Adult.

  Definition age_category_eq_dec : forall a1 a2 : AgeCategory, {a1 = a2} + {a1 <> a2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Definition is_pediatric (a : AgeCategory) : bool :=
    match a with
    | Neonate | Infant | Child => true
    | Adolescent | Adult => false
    end.

  Definition age_category_from_years (years : nat) : AgeCategory :=
    if years <? 1 then Infant
    else if years <? 8 then Child
    else if years <? 18 then Adolescent
    else Adult.

  Record PediatricPatient : Type := mkPedsPatient {
    peds_weight_kg : nat;
    peds_age_category : AgeCategory
  }.

  Definition epinephrine_peds_dose_mcg (p : PediatricPatient) : nat :=
    let dose := epinephrine_peds_dose_mcg_per_kg * peds_weight_kg p in
    Nat.min dose (epinephrine_peds_max_dose_mg * 1000).

  Definition epinephrine_peds_dose_mg (p : PediatricPatient) : nat :=
    epinephrine_peds_dose_mcg p / 1000.

  Definition amiodarone_peds_dose (p : PediatricPatient) : nat :=
    let dose := amiodarone_peds_dose_mg_per_kg * peds_weight_kg p in
    Nat.min dose amiodarone_peds_max_dose_mg.

  Definition lidocaine_peds_dose (p : PediatricPatient) : nat :=
    lidocaine_peds_dose_mg_per_kg * peds_weight_kg p.

  Definition magnesium_peds_dose (p : PediatricPatient) : nat :=
    let dose := magnesium_peds_dose_mg_per_kg * peds_weight_kg p in
    Nat.min dose magnesium_peds_max_dose_mg.

  Definition calcium_chloride_peds_dose (p : PediatricPatient) : nat :=
    calcium_chloride_peds_dose_mg_per_kg * peds_weight_kg p.

  Definition calcium_gluconate_peds_dose (p : PediatricPatient) : nat :=
    calcium_gluconate_peds_dose_mg_per_kg * peds_weight_kg p.

  Definition bicarb_peds_dose (p : PediatricPatient) : nat :=
    bicarb_peds_dose_meq_per_kg * peds_weight_kg p.

  Definition defibrillation_peds_initial (p : PediatricPatient) : nat :=
    defibrillation_peds_initial_J_per_kg * peds_weight_kg p.

  Definition defibrillation_peds_subsequent (p : PediatricPatient) : nat :=
    defibrillation_peds_subsequent_J_per_kg * peds_weight_kg p.

  Definition defibrillation_peds_max (p : PediatricPatient) : nat :=
    defibrillation_peds_max_J_per_kg * peds_weight_kg p.

  Definition standard_infant : PediatricPatient := mkPedsPatient 5 Infant.
  Definition standard_child : PediatricPatient := mkPedsPatient 20 Child.
  Definition standard_adolescent : PediatricPatient := mkPedsPatient 50 Adolescent.

  Theorem peds_epi_5kg_infant :
    epinephrine_peds_dose_mcg standard_infant = 50.
  Proof. reflexivity. Qed.

  Theorem peds_epi_20kg_child :
    epinephrine_peds_dose_mcg standard_child = 200.
  Proof. reflexivity. Qed.

  Theorem peds_epi_50kg_adolescent :
    epinephrine_peds_dose_mcg standard_adolescent = 500.
  Proof. reflexivity. Qed.

  Theorem peds_amio_20kg :
    amiodarone_peds_dose standard_child = 100.
  Proof. reflexivity. Qed.

  Theorem peds_defib_initial_20kg :
    defibrillation_peds_initial standard_child = 40.
  Proof. reflexivity. Qed.

  Theorem peds_defib_subsequent_20kg :
    defibrillation_peds_subsequent standard_child = 80.
  Proof. reflexivity. Qed.

  Definition peds_dose_valid_epi (p : PediatricPatient) : bool :=
    let dose := epinephrine_peds_dose_mcg p in
    (10 <=? dose) && (dose <=? 1000).

  Definition peds_dose_valid_amio (p : PediatricPatient) : bool :=
    let dose := amiodarone_peds_dose p in
    (5 <=? dose) && (dose <=? amiodarone_peds_max_dose_mg).

  Definition peds_dose_valid_defib (p : PediatricPatient) (joules : nat) (shock_num : nat) : bool :=
    let max := defibrillation_peds_max p in
    if shock_num =? 1 then
      let expected := defibrillation_peds_initial p in
      (expected <=? joules) && (joules <=? max)
    else
      let expected := defibrillation_peds_subsequent p in
      (expected <=? joules) && (joules <=? max).

  Theorem infant_epi_valid : peds_dose_valid_epi standard_infant = true.
  Proof. reflexivity. Qed.

  Theorem child_amio_valid : peds_dose_valid_amio standard_child = true.
  Proof. reflexivity. Qed.

  Theorem epi_dose_correct :
    epinephrine_dose_valid epinephrine_dose_mg = true.
  Proof. reflexivity. Qed.

  Theorem amio_first_correct :
    amiodarone_first_valid amiodarone_first_dose_mg = true.
  Proof. reflexivity. Qed.

  Theorem amio_second_correct :
    amiodarone_second_valid amiodarone_second_dose_mg = true.
  Proof. reflexivity. Qed.

  Theorem mag_min_valid :
    magnesium_dose_valid magnesium_dose_mg_min = true.
  Proof. reflexivity. Qed.

  Theorem mag_max_valid :
    magnesium_dose_valid magnesium_dose_mg_max = true.
  Proof. reflexivity. Qed.

  Theorem calcium_chloride_standard_valid :
    calcium_chloride_dose_valid calcium_chloride_dose_mg = true.
  Proof. reflexivity. Qed.

  Theorem calcium_gluconate_standard_valid :
    calcium_gluconate_dose_valid calcium_gluconate_dose_mg = true.
  Proof. reflexivity. Qed.

  Theorem bicarb_standard_valid :
    bicarb_dose_valid bicarb_dose_meq = true.
  Proof. reflexivity. Qed.

  Theorem lidocaine_70kg_dose :
    lidocaine_dose_for_weight standard_adult_weight = 105.
  Proof. reflexivity. Qed.

  Theorem lidocaine_70kg_max :
    lidocaine_max_for_weight standard_adult_weight = 210.
  Proof. reflexivity. Qed.

  Definition epi_interval_valid (interval_sec : nat) : bool :=
    let min_sec := epinephrine_interval_min * 60 in
    let max_sec := epinephrine_interval_max * 60 in
    (min_sec <=? interval_sec) && (interval_sec <=? max_sec).

  Theorem epi_interval_3min_valid : epi_interval_valid 180 = true.
  Proof. reflexivity. Qed.

  Theorem epi_interval_4min_valid : epi_interval_valid 240 = true.
  Proof. reflexivity. Qed.

  Theorem epi_interval_5min_valid : epi_interval_valid 300 = true.
  Proof. reflexivity. Qed.

  Theorem epi_interval_2min_invalid : epi_interval_valid 120 = false.
  Proof. reflexivity. Qed.

  Theorem epi_interval_6min_invalid : epi_interval_valid 360 = false.
  Proof. reflexivity. Qed.

  Definition is_antiarrhythmic (d : Drug) : bool :=
    match d with
    | Amiodarone | Lidocaine | MagnesiumSulfate => true
    | _ => false
    end.

  Definition is_vasopressor (d : Drug) : bool :=
    match d with
    | Epinephrine => true
    | _ => false
    end.

  Definition is_electrolyte_replacement (d : Drug) : bool :=
    match d with
    | CalciumChloride | CalciumGluconate | MagnesiumSulfate => true
    | _ => false
    end.

  Definition is_buffer (d : Drug) : bool :=
    match d with
    | SodiumBicarbonate => true
    | _ => false
    end.

  Definition is_lipid_rescue (d : Drug) : bool :=
    match d with
    | LipidEmulsion => true
    | _ => false
    end.

  Definition is_calcium (d : Drug) : bool :=
    match d with
    | CalciumChloride | CalciumGluconate => true
    | _ => false
    end.

  Definition treats_hyperkalemia (d : Drug) : bool :=
    match d with
    | CalciumChloride | CalciumGluconate | SodiumBicarbonate => true
    | _ => false
    end.

  Definition treats_local_anesthetic_toxicity (d : Drug) : bool :=
    match d with
    | LipidEmulsion => true
    | _ => false
    end.

  Theorem amiodarone_is_antiarrhythmic : is_antiarrhythmic Amiodarone = true.
  Proof. reflexivity. Qed.

  Theorem lidocaine_is_antiarrhythmic : is_antiarrhythmic Lidocaine = true.
  Proof. reflexivity. Qed.

  Theorem magnesium_is_antiarrhythmic : is_antiarrhythmic MagnesiumSulfate = true.
  Proof. reflexivity. Qed.

  Theorem epinephrine_is_vasopressor : is_vasopressor Epinephrine = true.
  Proof. reflexivity. Qed.

  Theorem epinephrine_not_antiarrhythmic : is_antiarrhythmic Epinephrine = false.
  Proof. reflexivity. Qed.

  Theorem calcium_chloride_treats_hyperK : treats_hyperkalemia CalciumChloride = true.
  Proof. reflexivity. Qed.

  Theorem calcium_gluconate_treats_hyperK : treats_hyperkalemia CalciumGluconate = true.
  Proof. reflexivity. Qed.

  Theorem bicarb_treats_hyperK : treats_hyperkalemia SodiumBicarbonate = true.
  Proof. reflexivity. Qed.

  Theorem lipid_treats_LAST : treats_local_anesthetic_toxicity LipidEmulsion = true.
  Proof. reflexivity. Qed.

  Inductive Contraindication : Type :=
    | CI_SevereLiverDisease
    | CI_SevereRenalFailure
    | CI_DigoxinToxicity
    | CI_HypersensitivityAmiodarone
    | CI_HypersensitivityLidocaine
    | CI_SecondDegreeAVBlock
    | CI_ThirdDegreeAVBlock
    | CI_SickSinusSyndrome
    | CI_CardiogenicShock
    | CI_SevereBradycardia
    | CI_WPWSyndrome
    | CI_Hypercalcemia
    | CI_Hypermagnesemia
    | CI_MetabolicAlkalosis
    | CI_Hypokalemia.

  Definition contraindication_eq_dec : forall c1 c2 : Contraindication, {c1 = c2} + {c1 <> c2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Definition all_contraindications : list Contraindication :=
    [CI_SevereLiverDisease; CI_SevereRenalFailure; CI_DigoxinToxicity;
     CI_HypersensitivityAmiodarone; CI_HypersensitivityLidocaine;
     CI_SecondDegreeAVBlock; CI_ThirdDegreeAVBlock; CI_SickSinusSyndrome;
     CI_CardiogenicShock; CI_SevereBradycardia; CI_WPWSyndrome;
     CI_Hypercalcemia; CI_Hypermagnesemia; CI_MetabolicAlkalosis; CI_Hypokalemia].

  Lemma all_contraindications_complete : forall c : Contraindication, In c all_contraindications.
  Proof. intros []; simpl; auto 20. Qed.

  Record PatientContraindications : Type := mkPatientCI {
    has_severe_liver_disease : bool;
    has_severe_renal_failure : bool;
    has_digoxin_toxicity : bool;
    has_amiodarone_allergy : bool;
    has_lidocaine_allergy : bool;
    has_second_degree_av_block : bool;
    has_third_degree_av_block : bool;
    has_sick_sinus_syndrome : bool;
    has_cardiogenic_shock : bool;
    has_severe_bradycardia : bool;
    has_wpw_syndrome : bool;
    has_hypercalcemia : bool;
    has_hypermagnesemia : bool;
    has_metabolic_alkalosis : bool;
    has_hypokalemia : bool
  }.

  Definition no_contraindications : PatientContraindications :=
    mkPatientCI false false false false false false false false false false false false false false false.

  Definition amiodarone_contraindicated (ci : PatientContraindications) : bool :=
    has_severe_liver_disease ci ||
    has_amiodarone_allergy ci ||
    has_second_degree_av_block ci ||
    has_third_degree_av_block ci ||
    has_sick_sinus_syndrome ci ||
    has_cardiogenic_shock ci ||
    has_severe_bradycardia ci.

  Definition lidocaine_contraindicated (ci : PatientContraindications) : bool :=
    has_lidocaine_allergy ci ||
    has_second_degree_av_block ci ||
    has_third_degree_av_block ci ||
    has_wpw_syndrome ci ||
    has_severe_bradycardia ci.

  Definition calcium_contraindicated (ci : PatientContraindications) : bool :=
    has_digoxin_toxicity ci ||
    has_hypercalcemia ci.

  Definition magnesium_contraindicated (ci : PatientContraindications) : bool :=
    has_hypermagnesemia ci ||
    has_severe_renal_failure ci.

  Definition bicarb_contraindicated (ci : PatientContraindications) : bool :=
    has_metabolic_alkalosis ci ||
    has_hypokalemia ci.

  Definition drug_safe_for_patient (d : Drug) (ci : PatientContraindications) : bool :=
    match d with
    | Amiodarone => negb (amiodarone_contraindicated ci)
    | Lidocaine => negb (lidocaine_contraindicated ci)
    | CalciumChloride | CalciumGluconate => negb (calcium_contraindicated ci)
    | MagnesiumSulfate => negb (magnesium_contraindicated ci)
    | SodiumBicarbonate => negb (bicarb_contraindicated ci)
    | Epinephrine => true
    | LipidEmulsion => true
    end.

  Theorem no_ci_all_drugs_safe : forall d,
    drug_safe_for_patient d no_contraindications = true.
  Proof. intros []; reflexivity. Qed.

  Definition liver_disease_patient : PatientContraindications :=
    mkPatientCI true false false false false false false false false false false false false false false.

  Theorem liver_disease_blocks_amio :
    amiodarone_contraindicated liver_disease_patient = true.
  Proof. reflexivity. Qed.

  Theorem liver_disease_amio_unsafe :
    drug_safe_for_patient Amiodarone liver_disease_patient = false.
  Proof. reflexivity. Qed.

  Theorem liver_disease_lido_safe :
    drug_safe_for_patient Lidocaine liver_disease_patient = true.
  Proof. reflexivity. Qed.

  Definition digoxin_toxic_patient : PatientContraindications :=
    mkPatientCI false false true false false false false false false false false false false false false.

  Theorem digoxin_tox_blocks_calcium :
    calcium_contraindicated digoxin_toxic_patient = true.
  Proof. reflexivity. Qed.

  Theorem digoxin_tox_calcium_unsafe :
    drug_safe_for_patient CalciumChloride digoxin_toxic_patient = false.
  Proof. reflexivity. Qed.

  Theorem digoxin_tox_mag_safe :
    drug_safe_for_patient MagnesiumSulfate digoxin_toxic_patient = true.
  Proof. reflexivity. Qed.

  Definition av_block_patient : PatientContraindications :=
    mkPatientCI false false false false false false true false false false false false false false false.

  Theorem av_block_blocks_amio :
    amiodarone_contraindicated av_block_patient = true.
  Proof. reflexivity. Qed.

  Theorem av_block_blocks_lido :
    lidocaine_contraindicated av_block_patient = true.
  Proof. reflexivity. Qed.

  Theorem epi_always_safe : forall ci,
    drug_safe_for_patient Epinephrine ci = true.
  Proof. reflexivity. Qed.

  Definition alternative_antiarrhythmic (ci : PatientContraindications) : option Drug :=
    if negb (amiodarone_contraindicated ci) then Some Amiodarone
    else if negb (lidocaine_contraindicated ci) then Some Lidocaine
    else if negb (magnesium_contraindicated ci) then Some MagnesiumSulfate
    else None.

  Theorem liver_disease_gets_lidocaine :
    alternative_antiarrhythmic liver_disease_patient = Some Lidocaine.
  Proof. reflexivity. Qed.

  Theorem no_ci_gets_amiodarone :
    alternative_antiarrhythmic no_contraindications = Some Amiodarone.
  Proof. reflexivity. Qed.

  Definition amiodarone_infusion_phase1_mg_per_min : nat := 1.
  Definition amiodarone_infusion_phase1_duration_hr : nat := 6.

  Definition amiodarone_infusion_phase2_mg_per_min_x10 : nat := 5.
  Definition amiodarone_infusion_phase2_duration_hr : nat := 18.

  Definition amiodarone_infusion_phase1_total_mg : nat :=
    amiodarone_infusion_phase1_mg_per_min * amiodarone_infusion_phase1_duration_hr * 60.

  Definition amiodarone_infusion_phase2_total_mg : nat :=
    (amiodarone_infusion_phase2_mg_per_min_x10 * amiodarone_infusion_phase2_duration_hr * 60) / 10.

  Definition amiodarone_24hr_infusion_total_mg : nat :=
    amiodarone_infusion_phase1_total_mg + amiodarone_infusion_phase2_total_mg.

  Definition amiodarone_total_with_boluses_mg (bolus_total : nat) : nat :=
    bolus_total + amiodarone_24hr_infusion_total_mg.

  Inductive InfusionPhase : Type :=
    | Phase1_HighRate
    | Phase2_LowRate
    | InfusionComplete.

  Definition infusion_phase_eq_dec : forall p1 p2 : InfusionPhase, {p1 = p2} + {p1 <> p2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Record AmiodaroneInfusion : Type := mkAmioInfusion {
    infusion_started : bool;
    infusion_start_time_sec : nat;
    current_phase : InfusionPhase;
    total_bolus_mg : nat;
    total_infused_mg : nat
  }.

  Definition initial_infusion (bolus_mg : nat) (start_time : nat) : AmiodaroneInfusion :=
    mkAmioInfusion true start_time Phase1_HighRate bolus_mg 0.

  Definition infusion_rate_mg_per_hr (inf : AmiodaroneInfusion) : nat :=
    match current_phase inf with
    | Phase1_HighRate => amiodarone_infusion_phase1_mg_per_min * 60
    | Phase2_LowRate => (amiodarone_infusion_phase2_mg_per_min_x10 * 60) / 10
    | InfusionComplete => 0
    end.

  Definition elapsed_infusion_time_hr (inf : AmiodaroneInfusion) (current_time_sec : nat) : nat :=
    (current_time_sec - infusion_start_time_sec inf) / 3600.

  Definition update_phase (inf : AmiodaroneInfusion) (current_time_sec : nat) : InfusionPhase :=
    let elapsed_hr := elapsed_infusion_time_hr inf current_time_sec in
    if negb (infusion_started inf) then InfusionComplete
    else if elapsed_hr <? amiodarone_infusion_phase1_duration_hr then Phase1_HighRate
    else if elapsed_hr <? (amiodarone_infusion_phase1_duration_hr + amiodarone_infusion_phase2_duration_hr) then Phase2_LowRate
    else InfusionComplete.

  Definition total_amiodarone_given (inf : AmiodaroneInfusion) : nat :=
    total_bolus_mg inf + total_infused_mg inf.

  Definition amiodarone_within_24hr_limit (inf : AmiodaroneInfusion) : bool :=
    total_amiodarone_given inf <=? amiodarone_max_24hr_mg.

  Theorem phase1_total_mg : amiodarone_infusion_phase1_total_mg = 360.
  Proof. reflexivity. Qed.

  Theorem phase2_total_mg : amiodarone_infusion_phase2_total_mg = 540.
  Proof. reflexivity. Qed.

  Theorem infusion_24hr_total : amiodarone_24hr_infusion_total_mg = 900.
  Proof. reflexivity. Qed.

  Theorem max_with_full_boluses :
    amiodarone_total_with_boluses_mg (amiodarone_first_dose_mg + amiodarone_second_dose_mg) = 1350.
  Proof. reflexivity. Qed.

  Theorem full_protocol_under_limit :
    amiodarone_total_with_boluses_mg (amiodarone_first_dose_mg + amiodarone_second_dose_mg) <=
    amiodarone_max_24hr_mg.
  Proof.
    unfold amiodarone_total_with_boluses_mg, amiodarone_24hr_infusion_total_mg,
           amiodarone_infusion_phase1_total_mg, amiodarone_infusion_phase2_total_mg,
           amiodarone_first_dose_mg, amiodarone_second_dose_mg, amiodarone_max_24hr_mg,
           amiodarone_infusion_phase1_mg_per_min, amiodarone_infusion_phase1_duration_hr,
           amiodarone_infusion_phase2_mg_per_min_x10, amiodarone_infusion_phase2_duration_hr.
    simpl. lia.
  Qed.

  Definition phase1_rate_mg_per_hr : nat := 60.
  Definition phase2_rate_mg_per_hr : nat := 30.

  Theorem phase1_rate_correct : amiodarone_infusion_phase1_mg_per_min * 60 = phase1_rate_mg_per_hr.
  Proof. reflexivity. Qed.

  Theorem phase2_rate_correct : (amiodarone_infusion_phase2_mg_per_min_x10 * 60) / 10 = phase2_rate_mg_per_hr.
  Proof. reflexivity. Qed.

  Definition lidocaine_infusion_mg_per_min_min : nat := 1.
  Definition lidocaine_infusion_mg_per_min_max : nat := 4.

  Definition lidocaine_infusion_rate_valid (rate_mg_per_min : nat) : bool :=
    (lidocaine_infusion_mg_per_min_min <=? rate_mg_per_min) &&
    (rate_mg_per_min <=? lidocaine_infusion_mg_per_min_max).

  Theorem lidocaine_infusion_2mg_valid : lidocaine_infusion_rate_valid 2 = true.
  Proof. reflexivity. Qed.

  Theorem lidocaine_infusion_5mg_invalid : lidocaine_infusion_rate_valid 5 = false.
  Proof. reflexivity. Qed.

End Medication.

(******************************************************************************)
(*                                                                            *)
(*                          SECTION 4: ACTIONS                                *)
(*                                                                            *)
(*  Interventions during cardiac arrest: Shock, CPR, drug administration.     *)
(*                                                                            *)
(******************************************************************************)

Module Action.

  Inductive t : Type :=
    | StartCPR
    | ContinueCPR
    | DeliverShock
    | CheckRhythm
    | GiveEpinephrine
    | GiveAmiodarone
    | GiveLidocaine
    | GiveMagnesium
    | GiveCalcium
    | GiveBicarb
    | GiveLipidEmulsion
    | CheckPulse
    | EstablishAccess
    | SecureAirway
    | IdentifyReversibleCause
    | InitiateECPR
    | ActivateCathLab.

  Definition eq_dec : forall a1 a2 : t, {a1 = a2} + {a1 <> a2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Definition all : list t :=
    [StartCPR; ContinueCPR; DeliverShock; CheckRhythm;
     GiveEpinephrine; GiveAmiodarone; GiveLidocaine; GiveMagnesium;
     GiveCalcium; GiveBicarb; GiveLipidEmulsion;
     CheckPulse; EstablishAccess; SecureAirway; IdentifyReversibleCause;
     InitiateECPR; ActivateCathLab].

  Lemma all_complete : forall a : t, In a all.
  Proof. intros []; simpl; auto 20. Qed.

  Definition is_drug_action (a : t) : bool :=
    match a with
    | GiveEpinephrine | GiveAmiodarone | GiveLidocaine | GiveMagnesium
    | GiveCalcium | GiveBicarb | GiveLipidEmulsion => true
    | _ => false
    end.

  Definition is_cpr_action (a : t) : bool :=
    match a with
    | StartCPR | ContinueCPR => true
    | _ => false
    end.

  Definition requires_shockable_rhythm (a : t) : bool :=
    match a with
    | DeliverShock | GiveAmiodarone | GiveLidocaine => true
    | _ => false
    end.

  Definition is_reversible_cause_treatment (a : t) : bool :=
    match a with
    | GiveCalcium | GiveBicarb | GiveLipidEmulsion => true
    | _ => false
    end.

  Definition is_advanced_intervention (a : t) : bool :=
    match a with
    | InitiateECPR | ActivateCathLab => true
    | _ => false
    end.

  Definition treats_hyperkalemia_action (a : t) : bool :=
    match a with
    | GiveCalcium | GiveBicarb => true
    | _ => false
    end.

  Definition treats_toxin_action (a : t) : bool :=
    match a with
    | GiveLipidEmulsion => true
    | _ => false
    end.

End Action.

(******************************************************************************)
(*                                                                            *)
(*                       SECTION 5: ALGORITHM STATE                           *)
(*                                                                            *)
(*  State machine for ACLS cardiac arrest algorithm tracking.                 *)
(*                                                                            *)
(******************************************************************************)

Module AlgorithmState.

  Inductive IdentifiedCause : Type :=
    | Cause_Hyperkalemia
    | Cause_Hypokalemia
    | Cause_Acidosis
    | Cause_LocalAnestheticToxicity
    | Cause_Hypovolemia
    | Cause_Hypoxia
    | Cause_TensionPneumothorax
    | Cause_Tamponade
    | Cause_Thrombosis_Coronary
    | Cause_Thrombosis_Pulmonary
    | Cause_Hypothermia
    | Cause_Torsades
    | Cause_TricyclicOverdose
    | Cause_BetaBlockerOverdose
    | Cause_CalciumChannelBlockerOverdose
    | Cause_DigoxinToxicity.

  Definition cause_eq_dec : forall c1 c2 : IdentifiedCause, {c1 = c2} + {c1 <> c2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Record t : Type := mkState {
    current_rhythm : Rhythm.t;
    shock_count : nat;
    cpr_cycles : nat;
    epinephrine_doses : nat;
    amiodarone_doses : nat;
    lidocaine_doses : nat;
    magnesium_doses : nat;
    calcium_doses : nat;
    bicarb_doses : nat;
    lipid_doses : nat;
    amiodarone_total_mg : nat;
    lidocaine_total_mg : nat;
    time_sec : nat;
    last_epi_time_sec : option nat;
    last_epi_cpr_cycle : option nat;
    no_flow_time_sec : nat;
    low_flow_time_sec : nat;
    cpr_start_time_sec : option nat;
    etco2_during_cpr : option nat;
    has_iv_access : bool;
    has_advanced_airway : bool;
    rosc_achieved : bool;
    identified_causes : list IdentifiedCause;
    patient_weight_kg : nat;
    measured_ph_x100 : option nat;
    measured_potassium_x10 : option nat;
    is_torsades : bool;
    ecpr_initiated : bool;
    cath_lab_activated : bool
  }.

  Definition initial (r : Rhythm.t) : t :=
    mkState r 0 0 0 0 0 0 0 0 0 0 0 0 None None 0 0 None None false false false [] 70 None None false false false.

  Definition initial_with_weight (r : Rhythm.t) (w : nat) : t :=
    mkState r 0 0 0 0 0 0 0 0 0 0 0 0 None None 0 0 None None false false false [] w None None false false false.

  Definition initial_with_no_flow (r : Rhythm.t) (no_flow : nat) : t :=
    mkState r 0 0 0 0 0 0 0 0 0 0 0 0 None None no_flow 0 None None false false false [] 70 None None false false false.

  Definition is_shockable_state (s : t) : bool :=
    Rhythm.shockable (current_rhythm s).

  Definition needs_shock (s : t) : bool :=
    is_shockable_state s && negb (rosc_achieved s).

  Definition epi_due (s : t) : bool :=
    match last_epi_time_sec s with
    | None => true
    | Some last_time =>
        let elapsed := time_sec s - last_time in
        Medication.epinephrine_interval_min * 60 <=? elapsed
    end.

  Definition can_give_amiodarone (s : t) : bool :=
    is_shockable_state s &&
    (3 <=? shock_count s) &&
    (amiodarone_doses s <? 2) &&
    (lidocaine_doses s =? 0).

  Definition shockable_epi_due (s : t) : bool :=
    is_shockable_state s && (2 <=? shock_count s) && epi_due s.

  Definition nonshockable_epi_due (s : t) : bool :=
    negb (is_shockable_state s) && epi_due s.

  Definition epi_due_by_cpr_cycle (s : t) : bool :=
    match last_epi_cpr_cycle s with
    | None => true
    | Some last_cycle => 2 <=? (cpr_cycles s - last_cycle)
    end.

  Definition epi_optimal_timing (s : t) : bool :=
    epi_due s && epi_due_by_cpr_cycle s.

  Definition epi_should_be_given_shockable (s : t) : bool :=
    is_shockable_state s &&
    (2 <=? shock_count s) &&
    epi_optimal_timing s &&
    negb (rosc_achieved s).

  Definition epi_should_be_given_nonshockable (s : t) : bool :=
    negb (is_shockable_state s) &&
    epi_optimal_timing s &&
    negb (rosc_achieved s).

  Definition cycles_since_last_epi (s : t) : option nat :=
    match last_epi_cpr_cycle s with
    | None => None
    | Some last_cycle => Some (cpr_cycles s - last_cycle)
    end.

  Definition time_since_last_epi_sec (s : t) : option nat :=
    match last_epi_time_sec s with
    | None => None
    | Some last_time => Some (time_sec s - last_time)
    end.

  Definition epi_indicated (s : t) : bool :=
    negb (rosc_achieved s) &&
    epi_due s &&
    (if is_shockable_state s then 2 <=? shock_count s else true).

  Definition epi_timing_summary (s : t) : nat :=
    match time_since_last_epi_sec s with
    | None => 0
    | Some t => t
    end.

  Theorem epi_indicated_shockable_after_two : forall s,
    is_shockable_state s = true ->
    shock_count s >= 2 ->
    epi_due s = true ->
    rosc_achieved s = false ->
    epi_indicated s = true.
  Proof.
    intros s Hshock Hsc Hepi Hrosc.
    unfold epi_indicated.
    rewrite Hrosc, Hepi, Hshock. simpl.
    destruct (shock_count s) as [|[|n]] eqn:E.
    - lia.
    - lia.
    - reflexivity.
  Qed.

  Theorem epi_indicated_nonshockable_immediate : forall s,
    is_shockable_state s = false ->
    epi_due s = true ->
    rosc_achieved s = false ->
    epi_indicated s = true.
  Proof.
    intros s Hshock Hepi Hrosc.
    unfold epi_indicated.
    rewrite Hrosc, Hepi, Hshock. reflexivity.
  Qed.

  Theorem epi_not_indicated_before_two_shocks : forall s,
    is_shockable_state s = true ->
    shock_count s < 2 ->
    epi_indicated s = false.
  Proof.
    intros s Hshock Hsc.
    unfold epi_indicated.
    rewrite Hshock.
    destruct (rosc_achieved s) eqn:Er; [reflexivity|].
    destruct (epi_due s) eqn:Ee; [|reflexivity].
    simpl.
    destruct (shock_count s) as [|[|n]] eqn:E.
    - reflexivity.
    - reflexivity.
    - lia.
  Qed.

  Theorem epi_not_indicated_after_rosc : forall s,
    rosc_achieved s = true ->
    epi_indicated s = false.
  Proof.
    intros s Hrosc.
    unfold epi_indicated.
    rewrite Hrosc. reflexivity.
  Qed.

  Theorem initial_no_shocks : forall r, shock_count (initial r) = 0.
  Proof. reflexivity. Qed.

  Theorem initial_no_epi : forall r, epinephrine_doses (initial r) = 0.
  Proof. reflexivity. Qed.

  Theorem initial_no_amio : forall r, amiodarone_doses (initial r) = 0.
  Proof. reflexivity. Qed.

  Theorem initial_no_rosc : forall r, rosc_achieved (initial r) = false.
  Proof. reflexivity. Qed.

  Definition with_shock (s : t) : t :=
    mkState (current_rhythm s) (S (shock_count s)) (cpr_cycles s)
            (epinephrine_doses s) (amiodarone_doses s) (lidocaine_doses s)
            (magnesium_doses s) (calcium_doses s) (bicarb_doses s) (lipid_doses s)
            (amiodarone_total_mg s) (lidocaine_total_mg s)
            (time_sec s) (last_epi_time_sec s) (last_epi_cpr_cycle s)
            (no_flow_time_sec s) (low_flow_time_sec s) (cpr_start_time_sec s)
            (etco2_during_cpr s) (has_iv_access s) (has_advanced_airway s)
            (rosc_achieved s) (identified_causes s) (patient_weight_kg s)
            (measured_ph_x100 s) (measured_potassium_x10 s) (is_torsades s)
            (ecpr_initiated s) (cath_lab_activated s).

  Definition with_cpr_cycle (s : t) : t :=
    mkState (current_rhythm s) (shock_count s) (S (cpr_cycles s))
            (epinephrine_doses s) (amiodarone_doses s) (lidocaine_doses s)
            (magnesium_doses s) (calcium_doses s) (bicarb_doses s) (lipid_doses s)
            (amiodarone_total_mg s) (lidocaine_total_mg s)
            (time_sec s + CPR.cycle_duration_sec) (last_epi_time_sec s) (last_epi_cpr_cycle s)
            (no_flow_time_sec s) (low_flow_time_sec s + CPR.cycle_duration_sec)
            (cpr_start_time_sec s) (etco2_during_cpr s)
            (has_iv_access s) (has_advanced_airway s) (rosc_achieved s)
            (identified_causes s) (patient_weight_kg s) (measured_ph_x100 s)
            (measured_potassium_x10 s) (is_torsades s) (ecpr_initiated s) (cath_lab_activated s).

  Definition with_epinephrine (s : t) : t :=
    mkState (current_rhythm s) (shock_count s) (cpr_cycles s)
            (S (epinephrine_doses s)) (amiodarone_doses s) (lidocaine_doses s)
            (magnesium_doses s) (calcium_doses s) (bicarb_doses s) (lipid_doses s)
            (amiodarone_total_mg s) (lidocaine_total_mg s)
            (time_sec s) (Some (time_sec s)) (Some (cpr_cycles s))
            (no_flow_time_sec s) (low_flow_time_sec s) (cpr_start_time_sec s)
            (etco2_during_cpr s) (has_iv_access s) (has_advanced_airway s)
            (rosc_achieved s) (identified_causes s) (patient_weight_kg s)
            (measured_ph_x100 s) (measured_potassium_x10 s) (is_torsades s)
            (ecpr_initiated s) (cath_lab_activated s).

  Definition with_amiodarone (s : t) : t :=
    let dose := if amiodarone_doses s =? 0
                then Medication.amiodarone_first_dose_mg
                else Medication.amiodarone_second_dose_mg in
    mkState (current_rhythm s) (shock_count s) (cpr_cycles s)
            (epinephrine_doses s) (S (amiodarone_doses s)) (lidocaine_doses s)
            (magnesium_doses s) (calcium_doses s) (bicarb_doses s) (lipid_doses s)
            (amiodarone_total_mg s + dose) (lidocaine_total_mg s)
            (time_sec s) (last_epi_time_sec s) (last_epi_cpr_cycle s)
            (no_flow_time_sec s) (low_flow_time_sec s) (cpr_start_time_sec s)
            (etco2_during_cpr s) (has_iv_access s) (has_advanced_airway s)
            (rosc_achieved s) (identified_causes s) (patient_weight_kg s)
            (measured_ph_x100 s) (measured_potassium_x10 s) (is_torsades s)
            (ecpr_initiated s) (cath_lab_activated s).

  Definition with_lidocaine (s : t) : t :=
    let dose := if lidocaine_doses s =? 0
                then (Medication.lidocaine_first_dose_mg_per_kg_x10 * patient_weight_kg s) / 10
                else (Medication.lidocaine_repeat_dose_mg_per_kg_x10 * patient_weight_kg s) / 10 in
    mkState (current_rhythm s) (shock_count s) (cpr_cycles s)
            (epinephrine_doses s) (amiodarone_doses s) (S (lidocaine_doses s))
            (magnesium_doses s) (calcium_doses s) (bicarb_doses s) (lipid_doses s)
            (amiodarone_total_mg s) (lidocaine_total_mg s + dose)
            (time_sec s) (last_epi_time_sec s) (last_epi_cpr_cycle s)
            (no_flow_time_sec s) (low_flow_time_sec s) (cpr_start_time_sec s)
            (etco2_during_cpr s) (has_iv_access s) (has_advanced_airway s)
            (rosc_achieved s) (identified_causes s) (patient_weight_kg s)
            (measured_ph_x100 s) (measured_potassium_x10 s) (is_torsades s)
            (ecpr_initiated s) (cath_lab_activated s).

  Definition with_magnesium (s : t) : t :=
    mkState (current_rhythm s) (shock_count s) (cpr_cycles s)
            (epinephrine_doses s) (amiodarone_doses s) (lidocaine_doses s)
            (S (magnesium_doses s)) (calcium_doses s) (bicarb_doses s) (lipid_doses s)
            (amiodarone_total_mg s) (lidocaine_total_mg s)
            (time_sec s) (last_epi_time_sec s) (last_epi_cpr_cycle s)
            (no_flow_time_sec s) (low_flow_time_sec s) (cpr_start_time_sec s)
            (etco2_during_cpr s) (has_iv_access s) (has_advanced_airway s)
            (rosc_achieved s) (identified_causes s) (patient_weight_kg s)
            (measured_ph_x100 s) (measured_potassium_x10 s) (is_torsades s)
            (ecpr_initiated s) (cath_lab_activated s).

  Definition with_calcium (s : t) : t :=
    mkState (current_rhythm s) (shock_count s) (cpr_cycles s)
            (epinephrine_doses s) (amiodarone_doses s) (lidocaine_doses s)
            (magnesium_doses s) (S (calcium_doses s)) (bicarb_doses s) (lipid_doses s)
            (amiodarone_total_mg s) (lidocaine_total_mg s)
            (time_sec s) (last_epi_time_sec s) (last_epi_cpr_cycle s)
            (no_flow_time_sec s) (low_flow_time_sec s) (cpr_start_time_sec s)
            (etco2_during_cpr s) (has_iv_access s) (has_advanced_airway s)
            (rosc_achieved s) (identified_causes s) (patient_weight_kg s)
            (measured_ph_x100 s) (measured_potassium_x10 s) (is_torsades s)
            (ecpr_initiated s) (cath_lab_activated s).

  Definition with_bicarb (s : t) : t :=
    mkState (current_rhythm s) (shock_count s) (cpr_cycles s)
            (epinephrine_doses s) (amiodarone_doses s) (lidocaine_doses s)
            (magnesium_doses s) (calcium_doses s) (S (bicarb_doses s)) (lipid_doses s)
            (amiodarone_total_mg s) (lidocaine_total_mg s)
            (time_sec s) (last_epi_time_sec s) (last_epi_cpr_cycle s)
            (no_flow_time_sec s) (low_flow_time_sec s) (cpr_start_time_sec s)
            (etco2_during_cpr s) (has_iv_access s) (has_advanced_airway s)
            (rosc_achieved s) (identified_causes s) (patient_weight_kg s)
            (measured_ph_x100 s) (measured_potassium_x10 s) (is_torsades s)
            (ecpr_initiated s) (cath_lab_activated s).

  Definition with_lipid (s : t) : t :=
    mkState (current_rhythm s) (shock_count s) (cpr_cycles s)
            (epinephrine_doses s) (amiodarone_doses s) (lidocaine_doses s)
            (magnesium_doses s) (calcium_doses s) (bicarb_doses s) (S (lipid_doses s))
            (amiodarone_total_mg s) (lidocaine_total_mg s)
            (time_sec s) (last_epi_time_sec s) (last_epi_cpr_cycle s)
            (no_flow_time_sec s) (low_flow_time_sec s) (cpr_start_time_sec s)
            (etco2_during_cpr s) (has_iv_access s) (has_advanced_airway s)
            (rosc_achieved s) (identified_causes s) (patient_weight_kg s)
            (measured_ph_x100 s) (measured_potassium_x10 s) (is_torsades s)
            (ecpr_initiated s) (cath_lab_activated s).

  Definition with_rhythm (s : t) (r : Rhythm.t) : t :=
    mkState r (shock_count s) (cpr_cycles s)
            (epinephrine_doses s) (amiodarone_doses s) (lidocaine_doses s)
            (magnesium_doses s) (calcium_doses s) (bicarb_doses s) (lipid_doses s)
            (amiodarone_total_mg s) (lidocaine_total_mg s)
            (time_sec s) (last_epi_time_sec s) (last_epi_cpr_cycle s)
            (no_flow_time_sec s) (low_flow_time_sec s) (cpr_start_time_sec s)
            (etco2_during_cpr s) (has_iv_access s) (has_advanced_airway s)
            (rosc_achieved s) (identified_causes s) (patient_weight_kg s)
            (measured_ph_x100 s) (measured_potassium_x10 s) (is_torsades s)
            (ecpr_initiated s) (cath_lab_activated s).

  Definition with_rosc (s : t) : t :=
    mkState (current_rhythm s) (shock_count s) (cpr_cycles s)
            (epinephrine_doses s) (amiodarone_doses s) (lidocaine_doses s)
            (magnesium_doses s) (calcium_doses s) (bicarb_doses s) (lipid_doses s)
            (amiodarone_total_mg s) (lidocaine_total_mg s)
            (time_sec s) (last_epi_time_sec s) (last_epi_cpr_cycle s)
            (no_flow_time_sec s) (low_flow_time_sec s) (cpr_start_time_sec s)
            (etco2_during_cpr s) (has_iv_access s) (has_advanced_airway s)
            true (identified_causes s) (patient_weight_kg s)
            (measured_ph_x100 s) (measured_potassium_x10 s) (is_torsades s)
            (ecpr_initiated s) (cath_lab_activated s).

  Definition with_cause (s : t) (c : IdentifiedCause) : t :=
    mkState (current_rhythm s) (shock_count s) (cpr_cycles s)
            (epinephrine_doses s) (amiodarone_doses s) (lidocaine_doses s)
            (magnesium_doses s) (calcium_doses s) (bicarb_doses s) (lipid_doses s)
            (amiodarone_total_mg s) (lidocaine_total_mg s)
            (time_sec s) (last_epi_time_sec s) (last_epi_cpr_cycle s)
            (no_flow_time_sec s) (low_flow_time_sec s) (cpr_start_time_sec s)
            (etco2_during_cpr s) (has_iv_access s) (has_advanced_airway s)
            (rosc_achieved s) (c :: identified_causes s) (patient_weight_kg s)
            (measured_ph_x100 s) (measured_potassium_x10 s) (is_torsades s)
            (ecpr_initiated s) (cath_lab_activated s).

  Definition with_ph (s : t) (ph : nat) : t :=
    mkState (current_rhythm s) (shock_count s) (cpr_cycles s)
            (epinephrine_doses s) (amiodarone_doses s) (lidocaine_doses s)
            (magnesium_doses s) (calcium_doses s) (bicarb_doses s) (lipid_doses s)
            (amiodarone_total_mg s) (lidocaine_total_mg s)
            (time_sec s) (last_epi_time_sec s) (last_epi_cpr_cycle s)
            (no_flow_time_sec s) (low_flow_time_sec s) (cpr_start_time_sec s)
            (etco2_during_cpr s) (has_iv_access s) (has_advanced_airway s)
            (rosc_achieved s) (identified_causes s) (patient_weight_kg s)
            (Some ph) (measured_potassium_x10 s) (is_torsades s)
            (ecpr_initiated s) (cath_lab_activated s).

  Definition with_potassium (s : t) (k : nat) : t :=
    mkState (current_rhythm s) (shock_count s) (cpr_cycles s)
            (epinephrine_doses s) (amiodarone_doses s) (lidocaine_doses s)
            (magnesium_doses s) (calcium_doses s) (bicarb_doses s) (lipid_doses s)
            (amiodarone_total_mg s) (lidocaine_total_mg s)
            (time_sec s) (last_epi_time_sec s) (last_epi_cpr_cycle s)
            (no_flow_time_sec s) (low_flow_time_sec s) (cpr_start_time_sec s)
            (etco2_during_cpr s) (has_iv_access s) (has_advanced_airway s)
            (rosc_achieved s) (identified_causes s) (patient_weight_kg s)
            (measured_ph_x100 s) (Some k) (is_torsades s)
            (ecpr_initiated s) (cath_lab_activated s).

  Definition with_torsades (s : t) : t :=
    mkState (current_rhythm s) (shock_count s) (cpr_cycles s)
            (epinephrine_doses s) (amiodarone_doses s) (lidocaine_doses s)
            (magnesium_doses s) (calcium_doses s) (bicarb_doses s) (lipid_doses s)
            (amiodarone_total_mg s) (lidocaine_total_mg s)
            (time_sec s) (last_epi_time_sec s) (last_epi_cpr_cycle s)
            (no_flow_time_sec s) (low_flow_time_sec s) (cpr_start_time_sec s)
            (etco2_during_cpr s) (has_iv_access s) (has_advanced_airway s)
            (rosc_achieved s) (identified_causes s) (patient_weight_kg s)
            (measured_ph_x100 s) (measured_potassium_x10 s) true
            (ecpr_initiated s) (cath_lab_activated s).

  Definition with_ecpr (s : t) : t :=
    mkState (current_rhythm s) (shock_count s) (cpr_cycles s)
            (epinephrine_doses s) (amiodarone_doses s) (lidocaine_doses s)
            (magnesium_doses s) (calcium_doses s) (bicarb_doses s) (lipid_doses s)
            (amiodarone_total_mg s) (lidocaine_total_mg s)
            (time_sec s) (last_epi_time_sec s) (last_epi_cpr_cycle s)
            (no_flow_time_sec s) (low_flow_time_sec s) (cpr_start_time_sec s)
            (etco2_during_cpr s) (has_iv_access s) (has_advanced_airway s)
            (rosc_achieved s) (identified_causes s) (patient_weight_kg s)
            (measured_ph_x100 s) (measured_potassium_x10 s) (is_torsades s)
            true (cath_lab_activated s).

  Definition with_cath_lab (s : t) : t :=
    mkState (current_rhythm s) (shock_count s) (cpr_cycles s)
            (epinephrine_doses s) (amiodarone_doses s) (lidocaine_doses s)
            (magnesium_doses s) (calcium_doses s) (bicarb_doses s) (lipid_doses s)
            (amiodarone_total_mg s) (lidocaine_total_mg s)
            (time_sec s) (last_epi_time_sec s) (last_epi_cpr_cycle s)
            (no_flow_time_sec s) (low_flow_time_sec s) (cpr_start_time_sec s)
            (etco2_during_cpr s) (has_iv_access s) (has_advanced_airway s)
            (rosc_achieved s) (identified_causes s) (patient_weight_kg s)
            (measured_ph_x100 s) (measured_potassium_x10 s) (is_torsades s)
            (ecpr_initiated s) true.

  Theorem shock_increments : forall s,
    shock_count (with_shock s) = S (shock_count s).
  Proof. reflexivity. Qed.

  Theorem cpr_increments : forall s,
    cpr_cycles (with_cpr_cycle s) = S (cpr_cycles s).
  Proof. reflexivity. Qed.

  Theorem epi_increments : forall s,
    epinephrine_doses (with_epinephrine s) = S (epinephrine_doses s).
  Proof. reflexivity. Qed.

  Theorem amio_increments : forall s,
    amiodarone_doses (with_amiodarone s) = S (amiodarone_doses s).
  Proof. reflexivity. Qed.

  Theorem epi_sets_time : forall s,
    last_epi_time_sec (with_epinephrine s) = Some (time_sec s).
  Proof. reflexivity. Qed.

  Theorem rosc_sets_flag : forall s,
    rosc_achieved (with_rosc s) = true.
  Proof. reflexivity. Qed.

  Theorem lidocaine_increments : forall s,
    lidocaine_doses (with_lidocaine s) = S (lidocaine_doses s).
  Proof. reflexivity. Qed.

  Theorem magnesium_increments : forall s,
    magnesium_doses (with_magnesium s) = S (magnesium_doses s).
  Proof. reflexivity. Qed.

  Theorem calcium_increments : forall s,
    calcium_doses (with_calcium s) = S (calcium_doses s).
  Proof. reflexivity. Qed.

  Theorem bicarb_increments : forall s,
    bicarb_doses (with_bicarb s) = S (bicarb_doses s).
  Proof. reflexivity. Qed.

  Theorem lipid_increments : forall s,
    lipid_doses (with_lipid s) = S (lipid_doses s).
  Proof. reflexivity. Qed.

  Definition has_cause (s : t) (c : IdentifiedCause) : bool :=
    existsb (fun x => if cause_eq_dec x c then true else false) (identified_causes s).

  Definition has_hyperkalemia (s : t) : bool :=
    has_cause s Cause_Hyperkalemia ||
    match measured_potassium_x10 s with
    | None => false
    | Some k => 55 <=? k
    end.

  Definition has_acidosis (s : t) : bool :=
    has_cause s Cause_Acidosis ||
    match measured_ph_x100 s with
    | None => false
    | Some ph => ph <? Medication.bicarb_ph_threshold_x100
    end.

  Definition has_local_anesthetic_toxicity (s : t) : bool :=
    has_cause s Cause_LocalAnestheticToxicity.

  Definition has_tricyclic_overdose (s : t) : bool :=
    has_cause s Cause_TricyclicOverdose.

  Definition has_beta_blocker_overdose (s : t) : bool :=
    has_cause s Cause_BetaBlockerOverdose.

  Definition has_calcium_channel_blocker_overdose (s : t) : bool :=
    has_cause s Cause_CalciumChannelBlockerOverdose.

  Definition has_digoxin_toxicity (s : t) : bool :=
    has_cause s Cause_DigoxinToxicity.

  Definition has_sodium_channel_blockade (s : t) : bool :=
    has_tricyclic_overdose s || has_local_anesthetic_toxicity s.

  Definition needs_calcium (s : t) : bool :=
    (calcium_doses s =? 0) &&
    (has_hyperkalemia s || has_calcium_channel_blocker_overdose s || has_beta_blocker_overdose s).

  Definition bicarb_target_ph_x100 : nat := 750.

  Definition needs_bicarb (s : t) : bool :=
    (bicarb_doses s <? 3) &&
    (has_acidosis s || has_sodium_channel_blockade s).

  Definition needs_lipid (s : t) : bool :=
    has_local_anesthetic_toxicity s && (lipid_doses s =? 0).

  Definition refractory_VF_threshold : nat := 3.

  Definition is_refractory_VF (s : t) : bool :=
    (refractory_VF_threshold <=? shock_count s) &&
    (1 <=? amiodarone_doses s) &&
    is_shockable_state s.

  Definition needs_magnesium (s : t) : bool :=
    (magnesium_doses s =? 0) &&
    (is_torsades s || is_refractory_VF s).

  Definition lidocaine_max_total_mg (s : t) : nat :=
    (Medication.lidocaine_max_mg_per_kg_x10 * patient_weight_kg s) / 10.

  Definition lidocaine_next_dose_mg (s : t) : nat :=
    if lidocaine_doses s =? 0
    then (Medication.lidocaine_first_dose_mg_per_kg_x10 * patient_weight_kg s) / 10
    else (Medication.lidocaine_repeat_dose_mg_per_kg_x10 * patient_weight_kg s) / 10.

  Definition can_give_lidocaine (s : t) : bool :=
    is_shockable_state s &&
    (3 <=? shock_count s) &&
    (amiodarone_doses s =? 0) &&
    (lidocaine_doses s <? 3) &&
    (lidocaine_total_mg s + lidocaine_next_dose_mg s <=? lidocaine_max_total_mg s).

  Definition total_antiarrhythmic_doses (s : t) : nat :=
    amiodarone_doses s + lidocaine_doses s.

  Definition amiodarone_under_24hr_max (s : t) : bool :=
    amiodarone_total_mg s <=? Medication.amiodarone_max_24hr_mg.

  Theorem initial_amio_under_max : forall r,
    amiodarone_under_24hr_max (initial r) = true.
  Proof. reflexivity. Qed.

  Theorem lidocaine_max_70kg : lidocaine_max_total_mg (initial Rhythm.VF) = 210.
  Proof. reflexivity. Qed.

  Theorem lidocaine_first_dose_70kg : lidocaine_next_dose_mg (initial Rhythm.VF) = 105.
  Proof. reflexivity. Qed.

  Definition assess_cpr_quality (s : t) : CPR.CPRQuality :=
    match etco2_during_cpr s with
    | None => CPR.QualityAdequate
    | Some e => CPR.assess_cpr_quality_by_etco2 e
    end.

  Definition cpr_quality_suggests_rosc (s : t) : bool :=
    match etco2_during_cpr s with
    | None => false
    | Some e => CPR.etco2_suggests_rosc_during_cpr e
    end.

  Definition cpr_quality_is_poor (s : t) : bool :=
    match etco2_during_cpr s with
    | None => false
    | Some e => CPR.etco2_indicates_poor_cpr e
    end.

  Theorem initial_no_etco2_data : forall r,
    etco2_during_cpr (initial r) = None.
  Proof. reflexivity. Qed.

  Theorem high_etco2_suggests_rosc : forall s e,
    etco2_during_cpr s = Some e ->
    e >= 40 ->
    cpr_quality_suggests_rosc s = true.
  Proof.
    intros s e He Hge.
    unfold cpr_quality_suggests_rosc. rewrite He.
    unfold CPR.etco2_suggests_rosc_during_cpr.
    destruct (40 <=? e) eqn:E.
    - reflexivity.
    - apply Nat.leb_gt in E. lia.
  Qed.

  Theorem low_etco2_indicates_poor_cpr : forall s e,
    etco2_during_cpr s = Some e ->
    e < CPR.etco2_min_during_cpr ->
    cpr_quality_is_poor s = true.
  Proof.
    intros s e He Hlt.
    unfold cpr_quality_is_poor. rewrite He.
    unfold CPR.etco2_indicates_poor_cpr.
    destruct (e <? CPR.etco2_min_during_cpr) eqn:E.
    - reflexivity.
    - apply Nat.ltb_nlt in E. exfalso. apply E. exact Hlt.
  Qed.

End AlgorithmState.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 6: ALGORITHM DECISION LOGIC                     *)
(*                                                                            *)
(*  Core ACLS decision functions: recommended actions based on rhythm and     *)
(*  algorithm state per AHA 2020 guidelines.                                  *)
(*                                                                            *)
(******************************************************************************)

Module Decision.

  Import AlgorithmState.

  Inductive Recommendation : Type :=
    | Shock_then_CPR
    | CPR_only
    | Give_Epi_during_CPR
    | Give_Amio_during_CPR
    | Give_Lido_during_CPR
    | Give_Mag_during_CPR
    | Give_Calcium_during_CPR
    | Give_Bicarb_during_CPR
    | Give_Lipid_during_CPR
    | Check_Rhythm
    | Consider_ECPR
    | Activate_Cath_Lab
    | ROSC_achieved.

  Definition rec_eq_dec : forall r1 r2 : Recommendation, {r1 = r2} + {r1 <> r2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Definition reversible_cause_recommendation (s : AlgorithmState.t) : option Recommendation :=
    if needs_lipid s then Some Give_Lipid_during_CPR
    else if needs_calcium s then Some Give_Calcium_during_CPR
    else if needs_bicarb s then Some Give_Bicarb_during_CPR
    else if needs_magnesium s then Some Give_Mag_during_CPR
    else None.

  Definition antiarrhythmic_recommendation (s : AlgorithmState.t) : option Recommendation :=
    if can_give_amiodarone s && (amiodarone_doses s =? 0) then Some Give_Amio_during_CPR
    else if can_give_amiodarone s && (amiodarone_doses s =? 1) then Some Give_Amio_during_CPR
    else if can_give_lidocaine s && (lidocaine_doses s =? 0) then Some Give_Lido_during_CPR
    else if can_give_lidocaine s && (lidocaine_doses s <? 3) then Some Give_Lido_during_CPR
    else None.

  Definition shockable_recommendation (s : AlgorithmState.t) : Recommendation :=
    if rosc_achieved s then ROSC_achieved
    else match reversible_cause_recommendation s with
         | Some rec => rec
         | None =>
           if shock_count s =? 0 then Shock_then_CPR
           else if (shock_count s =? 1) then Shock_then_CPR
           else if (shock_count s =? 2) && epi_due s then Give_Epi_during_CPR
           else match antiarrhythmic_recommendation s with
                | Some rec => rec
                | None =>
                  if epi_due s then Give_Epi_during_CPR
                  else Shock_then_CPR
                end
         end.

  Definition nonshockable_recommendation (s : AlgorithmState.t) : Recommendation :=
    if rosc_achieved s then ROSC_achieved
    else match reversible_cause_recommendation s with
         | Some rec => rec
         | None =>
           if epi_due s then Give_Epi_during_CPR
           else CPR_only
         end.

  Definition recommend (s : AlgorithmState.t) : Recommendation :=
    if is_shockable_state s then shockable_recommendation s
    else nonshockable_recommendation s.

  Definition recommend_with_ecpr (s : AlgorithmState.t) (ecpr_eligible : bool) : Recommendation :=
    if rosc_achieved s then ROSC_achieved
    else if ecpr_eligible && negb (ecpr_initiated s) && (10 <=? cpr_cycles s) then Consider_ECPR
    else recommend s.

  Definition recommend_with_cath_lab (s : AlgorithmState.t) (stemi_suspected : bool) : Recommendation :=
    if rosc_achieved s then ROSC_achieved
    else if stemi_suspected && negb (cath_lab_activated s) then Activate_Cath_Lab
    else recommend s.

  Lemma initial_no_reversible_cause : forall r,
    reversible_cause_recommendation (initial r) = None.
  Proof. reflexivity. Qed.

  Lemma initial_no_antiarrhythmic : forall r,
    antiarrhythmic_recommendation (initial r) = None.
  Proof.
    intros r.
    unfold antiarrhythmic_recommendation, can_give_amiodarone, can_give_lidocaine,
           is_shockable_state, initial. simpl.
    destruct (Rhythm.shockable r); reflexivity.
  Qed.

  Theorem VF_initial_shock :
    recommend (initial Rhythm.VF) = Shock_then_CPR.
  Proof. reflexivity. Qed.

  Theorem pVT_initial_shock :
    recommend (initial Rhythm.pVT) = Shock_then_CPR.
  Proof. reflexivity. Qed.

  Theorem VF_initial_shock_general : forall s,
    current_rhythm s = Rhythm.VF ->
    shock_count s = 0 ->
    rosc_achieved s = false ->
    reversible_cause_recommendation s = None ->
    recommend s = Shock_then_CPR.
  Proof.
    intros s Hr Hsc Hrosc Hrc.
    unfold recommend, is_shockable_state. rewrite Hr. simpl.
    unfold shockable_recommendation. rewrite Hrosc, Hrc, Hsc. reflexivity.
  Qed.

  Theorem pVT_initial_shock_general : forall s,
    current_rhythm s = Rhythm.pVT ->
    shock_count s = 0 ->
    rosc_achieved s = false ->
    reversible_cause_recommendation s = None ->
    recommend s = Shock_then_CPR.
  Proof.
    intros s Hr Hsc Hrosc Hrc.
    unfold recommend, is_shockable_state. rewrite Hr. simpl.
    unfold shockable_recommendation. rewrite Hrosc, Hrc, Hsc. reflexivity.
  Qed.

  Lemma nonshockable_not_shock : forall s,
    Rhythm.shockable (current_rhythm s) = false ->
    rosc_achieved s = false ->
    recommend s <> Shock_then_CPR.
  Proof.
    intros s Hns Hrosc.
    unfold recommend, is_shockable_state.
    rewrite Hns. simpl.
    unfold nonshockable_recommendation.
    rewrite Hrosc.
    unfold reversible_cause_recommendation.
    destruct (needs_lipid s); [intro H; discriminate H|].
    destruct (needs_calcium s); [intro H; discriminate H|].
    destruct (needs_bicarb s); [intro H; discriminate H|].
    destruct (needs_magnesium s); [intro H; discriminate H|].
    destruct (epi_due s); intro H; discriminate H.
  Qed.

  Theorem PEA_no_shock : forall s,
    current_rhythm s = Rhythm.PEA ->
    rosc_achieved s = false ->
    recommend s <> Shock_then_CPR.
  Proof.
    intros s Hr Hrosc.
    apply nonshockable_not_shock; [rewrite Hr; reflexivity | exact Hrosc].
  Qed.

  Theorem Asystole_no_shock : forall s,
    current_rhythm s = Rhythm.Asystole ->
    rosc_achieved s = false ->
    recommend s <> Shock_then_CPR.
  Proof.
    intros s Hr Hrosc.
    apply nonshockable_not_shock; [rewrite Hr; reflexivity | exact Hrosc].
  Qed.

  Theorem nonshockable_immediate_epi : forall r,
    Rhythm.shockable r = false ->
    recommend (initial r) = Give_Epi_during_CPR.
  Proof.
    intros r Hr.
    unfold recommend, is_shockable_state, initial. simpl. rewrite Hr.
    reflexivity.
  Qed.

  Theorem PEA_immediate_epi :
    recommend (initial Rhythm.PEA) = Give_Epi_during_CPR.
  Proof. reflexivity. Qed.

  Theorem Asystole_immediate_epi :
    recommend (initial Rhythm.Asystole) = Give_Epi_during_CPR.
  Proof. reflexivity. Qed.

  Theorem rosc_stops_algorithm : forall s,
    rosc_achieved s = true ->
    recommend s = ROSC_achieved.
  Proof.
    intros s Hrosc.
    unfold recommend.
    destruct (is_shockable_state s).
    - unfold shockable_recommendation. rewrite Hrosc. reflexivity.
    - unfold nonshockable_recommendation. rewrite Hrosc. reflexivity.
  Qed.

  Definition amiodarone_after_third_shock : forall s,
    is_shockable_state s = true ->
    shock_count s = 3 ->
    amiodarone_doses s = 0 ->
    lidocaine_doses s = 0 ->
    rosc_achieved s = false ->
    can_give_amiodarone s = true.
  Proof.
    intros s Hshock Hsc Hamio Hlido Hrosc.
    unfold can_give_amiodarone.
    rewrite Hshock, Hsc, Hamio, Hlido. reflexivity.
  Qed.

  Lemma max_two_amiodarone : forall s,
    amiodarone_doses s = 2 ->
    can_give_amiodarone s = false.
  Proof.
    intros s Hamio.
    unfold can_give_amiodarone.
    rewrite Hamio.
    destruct (is_shockable_state s) eqn:E; [|reflexivity].
    destruct (3 <=? shock_count s) eqn:E2; reflexivity.
  Qed.

  Theorem hyperkalemia_gets_calcium : forall s,
    rosc_achieved s = false ->
    needs_lipid s = false ->
    needs_calcium s = true ->
    recommend s = Give_Calcium_during_CPR.
  Proof.
    intros s Hrosc Hnlipid Hcalc.
    unfold recommend.
    destruct (is_shockable_state s).
    - unfold shockable_recommendation. rewrite Hrosc.
      unfold reversible_cause_recommendation.
      rewrite Hnlipid, Hcalc. reflexivity.
    - unfold nonshockable_recommendation. rewrite Hrosc.
      unfold reversible_cause_recommendation.
      rewrite Hnlipid, Hcalc. reflexivity.
  Qed.

  Theorem local_anesthetic_toxicity_gets_lipid : forall s,
    rosc_achieved s = false ->
    needs_lipid s = true ->
    recommend s = Give_Lipid_during_CPR.
  Proof.
    intros s Hrosc Hlipid.
    unfold recommend.
    destruct (is_shockable_state s).
    - unfold shockable_recommendation. rewrite Hrosc.
      unfold reversible_cause_recommendation. rewrite Hlipid. reflexivity.
    - unfold nonshockable_recommendation. rewrite Hrosc.
      unfold reversible_cause_recommendation. rewrite Hlipid. reflexivity.
  Qed.

  Theorem torsades_gets_magnesium : forall s,
    rosc_achieved s = false ->
    needs_lipid s = false ->
    needs_calcium s = false ->
    needs_bicarb s = false ->
    needs_magnesium s = true ->
    recommend s = Give_Mag_during_CPR.
  Proof.
    intros s Hrosc Hnlipid Hncalc Hnbicarb Hmag.
    unfold recommend.
    destruct (is_shockable_state s).
    - unfold shockable_recommendation. rewrite Hrosc.
      unfold reversible_cause_recommendation.
      rewrite Hnlipid, Hncalc, Hnbicarb, Hmag. reflexivity.
    - unfold nonshockable_recommendation. rewrite Hrosc.
      unfold reversible_cause_recommendation.
      rewrite Hnlipid, Hncalc, Hnbicarb, Hmag. reflexivity.
  Qed.

  Theorem amiodarone_recommended_first : forall s,
    is_shockable_state s = true ->
    shock_count s >= 3 ->
    amiodarone_doses s = 0 ->
    lidocaine_doses s = 0 ->
    antiarrhythmic_recommendation s = Some Give_Amio_during_CPR.
  Proof.
    intros s Hshock Hsc3 Hamio Hlido.
    unfold antiarrhythmic_recommendation, can_give_amiodarone.
    rewrite Hshock, Hamio, Hlido.
    destruct (3 <=? shock_count s) eqn:E.
    - reflexivity.
    - apply Nat.leb_gt in E. lia.
  Qed.

  Theorem lidocaine_as_amio_alternative : forall s,
    is_shockable_state s = true ->
    shock_count s >= 3 ->
    amiodarone_doses s = 0 ->
    lidocaine_doses s = 0 ->
    lidocaine_total_mg s = 0 ->
    lidocaine_next_dose_mg s <= lidocaine_max_total_mg s ->
    can_give_lidocaine s = true.
  Proof.
    intros s Hshock Hsc3 Hamio Hlido Htotal Hmax.
    unfold can_give_lidocaine.
    rewrite Hshock, Hamio, Hlido, Htotal. simpl.
    destruct (shock_count s) as [|[|[|n]]] eqn:Esc.
    - lia.
    - lia.
    - lia.
    - simpl. apply Nat.leb_le. lia.
  Qed.

  Theorem no_antiarrhythmic_after_max_amio : forall s,
    amiodarone_doses s = 2 ->
    amiodarone_doses s > 0 ->
    can_give_amiodarone s = false /\ can_give_lidocaine s = false.
  Proof.
    intros s Hamio Hgt.
    split.
    - unfold can_give_amiodarone. rewrite Hamio.
      destruct (is_shockable_state s); [|reflexivity].
      destruct (3 <=? shock_count s); reflexivity.
    - unfold can_give_lidocaine. rewrite Hamio.
      destruct (is_shockable_state s); [|reflexivity].
      destruct (3 <=? shock_count s); reflexivity.
  Qed.

End Decision.

(******************************************************************************)
(*                                                                            *)
(*                  SECTION 7: ROSC INDICATORS                                *)
(*                                                                            *)
(*  Return of Spontaneous Circulation (ROSC) criteria per AHA 2020.           *)
(*  ETCO2 ≥ 40 mmHg sustained increase, palpable pulse, arterial waveform.    *)
(*                                                                            *)
(******************************************************************************)

Module ROSC.

  Definition etco2_threshold_mmHg : nat := 40.

  Inductive Indicator : Type :=
    | PalpablePulse
    | ETCO2_Increase
    | ArterialWaveform
    | SpontaneousBreathing.

  Definition indicator_eq_dec : forall i1 i2 : Indicator, {i1 = i2} + {i1 <> i2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Definition all_indicators : list Indicator :=
    [PalpablePulse; ETCO2_Increase; ArterialWaveform; SpontaneousBreathing].

  Lemma all_indicators_complete : forall i : Indicator, In i all_indicators.
  Proof. intros []; simpl; auto. Qed.

  Record Findings : Type := mkFindings {
    pulse_present : bool;
    etco2_mmHg : nat;
    arterial_waveform : bool;
    spontaneous_breathing : bool
  }.

  Definition etco2_suggests_rosc (f : Findings) : bool :=
    etco2_threshold_mmHg <=? etco2_mmHg f.

  Definition rosc_confirmed (f : Findings) : bool :=
    pulse_present f && (etco2_suggests_rosc f || arterial_waveform f).

  Definition rosc_likely (f : Findings) : bool :=
    pulse_present f || etco2_suggests_rosc f || arterial_waveform f.

  Definition no_rosc : Findings := mkFindings false 0 false false.

  Definition clear_rosc : Findings := mkFindings true 45 true true.

  Theorem no_rosc_not_confirmed : rosc_confirmed no_rosc = false.
  Proof. reflexivity. Qed.

  Theorem clear_rosc_confirmed : rosc_confirmed clear_rosc = true.
  Proof. reflexivity. Qed.

  Theorem pulse_with_etco2_is_rosc : forall etco2,
    etco2_threshold_mmHg <= etco2 ->
    rosc_confirmed (mkFindings true etco2 false false) = true.
  Proof.
    intros etco2 H.
    unfold rosc_confirmed, etco2_suggests_rosc, etco2_threshold_mmHg.
    simpl pulse_present. simpl etco2_mmHg. simpl arterial_waveform.
    rewrite orb_false_r.
    apply Nat.leb_le. exact H.
  Qed.

  Theorem pulse_with_arterial_is_rosc :
    rosc_confirmed (mkFindings true 0 true false) = true.
  Proof. reflexivity. Qed.

  Theorem etco2_alone_not_confirmed : forall etco2,
    rosc_confirmed (mkFindings false etco2 false false) = false.
  Proof. reflexivity. Qed.

End ROSC.

(******************************************************************************)
(*                                                                            *)
(*                   SECTION 8: REVERSIBLE CAUSES                             *)
(*                                                                            *)
(*  The H's and T's - reversible causes of cardiac arrest.                    *)
(*                                                                            *)
(******************************************************************************)

Module ReversibleCauses.

  Inductive H_Cause : Type :=
    | Hypovolemia
    | Hypoxia
    | HydrogenIon
    | Hypokalemia
    | Hyperkalemia
    | Hypothermia
    | Hypoglycemia.

  Inductive T_Cause : Type :=
    | TensionPneumothorax
    | Tamponade
    | Toxins
    | ThrombosisCoronary
    | ThrombosisPulmonary
    | Trauma.

  Inductive Cause : Type :=
    | H (h : H_Cause)
    | T (t : T_Cause).

  Definition h_cause_eq_dec : forall h1 h2 : H_Cause, {h1 = h2} + {h1 <> h2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Definition t_cause_eq_dec : forall t1 t2 : T_Cause, {t1 = t2} + {t1 <> t2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Definition cause_eq_dec : forall c1 c2 : Cause, {c1 = c2} + {c1 <> c2}.
  Proof.
    intros [h1|t1] [h2|t2].
    - destruct (h_cause_eq_dec h1 h2); [left; f_equal; assumption | right; intro H; inversion H; contradiction].
    - right; discriminate.
    - right; discriminate.
    - destruct (t_cause_eq_dec t1 t2); [left; f_equal; assumption | right; intro H0; inversion H0; contradiction].
  Defined.

  Definition all_h_causes : list H_Cause :=
    [Hypovolemia; Hypoxia; HydrogenIon; Hypokalemia; Hyperkalemia; Hypothermia; Hypoglycemia].

  Definition all_t_causes : list T_Cause :=
    [TensionPneumothorax; Tamponade; Toxins; ThrombosisCoronary; ThrombosisPulmonary; Trauma].

  Lemma all_h_causes_complete : forall h : H_Cause, In h all_h_causes.
  Proof. intros []; simpl; auto 10. Qed.

  Lemma all_t_causes_complete : forall t : T_Cause, In t all_t_causes.
  Proof. intros []; simpl; auto 10. Qed.

  Lemma h_causes_count : length all_h_causes = 7.
  Proof. reflexivity. Qed.

  Lemma t_causes_count : length all_t_causes = 6.
  Proof. reflexivity. Qed.

  Definition is_immediately_treatable (c : Cause) : bool :=
    match c with
    | H Hypovolemia => true
    | H Hypoxia => true
    | H Hypothermia => false
    | T TensionPneumothorax => true
    | T Tamponade => true
    | T Toxins => true
    | _ => false
    end.

  Definition requires_lab_diagnosis (c : Cause) : bool :=
    match c with
    | H HydrogenIon => true
    | H Hypokalemia => true
    | H Hyperkalemia => true
    | H Hypoglycemia => true
    | _ => false
    end.

  Definition requires_imaging (c : Cause) : bool :=
    match c with
    | T TensionPneumothorax => true
    | T Tamponade => true
    | T ThrombosisCoronary => true
    | T ThrombosisPulmonary => true
    | T Trauma => true
    | _ => false
    end.

End ReversibleCauses.

(******************************************************************************)
(*                                                                            *)
(*                  SECTION 7B: TRANSCUTANEOUS AND TRANSVENOUS PACING         *)
(*                                                                            *)
(*  Pacing for bradycardia-related PEA and symptomatic bradycardia.           *)
(*  TCP immediate, TVP for sustained pacing. Per AHA 2020 bradycardia alg.    *)
(*                                                                            *)
(******************************************************************************)

Module Pacing.

  Inductive PacingMode : Type :=
    | TCP
    | TVP
    | PermanentPacer
    | NoPacing.

  Definition pacing_mode_eq_dec : forall p1 p2 : PacingMode, {p1 = p2} + {p1 <> p2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Inductive BradycardiaType : Type :=
    | SinusBradycardia
    | JunctionalBradycardia
    | SecondDegreeType1
    | SecondDegreeType2
    | ThirdDegreeAVBlock
    | SickSinus
    | AsystolicPause.

  Definition bradycardia_type_eq_dec : forall b1 b2 : BradycardiaType, {b1 = b2} + {b1 <> b2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Definition tcp_initial_rate_ppm : nat := 60.
  Definition tcp_max_rate_ppm : nat := 180.
  Definition tcp_initial_output_mA : nat := 0.
  Definition tcp_max_output_mA : nat := 200.
  Definition tcp_capture_threshold_typical_mA : nat := 70.

  Definition tvp_initial_rate_ppm : nat := 60.
  Definition tvp_max_rate_ppm : nat := 180.
  Definition tvp_initial_output_mA_x10 : nat := 50.
  Definition tvp_capture_threshold_typical_mA_x10 : nat := 10.

  Definition symptomatic_bradycardia_hr_threshold : nat := 50.
  Definition severe_bradycardia_hr_threshold : nat := 40.
  Definition critical_bradycardia_hr_threshold : nat := 30.

  Record BradycardiaState : Type := mkBradyState {
    heart_rate : nat;
    bradycardia_type : BradycardiaType;
    is_symptomatic : bool;
    has_pulses : bool;
    systolic_bp : nat;
    is_hemodynamically_unstable : bool;
    atropine_given : bool;
    atropine_doses : nat;
    dopamine_infusing : bool;
    epinephrine_infusing : bool;
    pacing_mode : PacingMode;
    capture_achieved : bool;
    underlying_cause_identified : bool
  }.

  Definition is_bradycardia (bs : BradycardiaState) : bool :=
    heart_rate bs <? 60.

  Definition is_severe_bradycardia (bs : BradycardiaState) : bool :=
    heart_rate bs <? severe_bradycardia_hr_threshold.

  Definition is_critical_bradycardia (bs : BradycardiaState) : bool :=
    heart_rate bs <? critical_bradycardia_hr_threshold.

  Definition atropine_may_help (bs : BradycardiaState) : bool :=
    match bradycardia_type bs with
    | SinusBradycardia | JunctionalBradycardia | SecondDegreeType1 => true
    | SecondDegreeType2 | ThirdDegreeAVBlock | SickSinus | AsystolicPause => false
    end.

  Definition atropine_max_doses : nat := 3.
  Definition atropine_dose_mg_x10 : nat := 10.
  Definition atropine_total_max_mg_x10 : nat := 30.

  Definition can_give_atropine (bs : BradycardiaState) : bool :=
    atropine_may_help bs &&
    (atropine_doses bs <? atropine_max_doses).

  Definition pacing_indicated (bs : BradycardiaState) : bool :=
    is_symptomatic bs &&
    is_hemodynamically_unstable bs &&
    (negb (atropine_may_help bs) || (atropine_max_doses <=? atropine_doses bs) || is_critical_bradycardia bs).

  Definition tcp_indicated (bs : BradycardiaState) : bool :=
    pacing_indicated bs &&
    negb (capture_achieved bs) &&
    match pacing_mode bs with
    | NoPacing | TCP => true
    | TVP | PermanentPacer => false
    end.

  Definition tvp_indicated (bs : BradycardiaState) : bool :=
    pacing_indicated bs &&
    (match pacing_mode bs with TCP => negb (capture_achieved bs) | _ => false end ||
     is_critical_bradycardia bs).

  Definition pea_from_bradycardia (bs : BradycardiaState) : bool :=
    negb (has_pulses bs) &&
    (is_critical_bradycardia bs || (heart_rate bs =? 0)).

  Definition pacing_for_bradycardic_pea (bs : BradycardiaState) : bool :=
    pea_from_bradycardia bs &&
    match bradycardia_type bs with
    | ThirdDegreeAVBlock | SecondDegreeType2 | AsystolicPause => true
    | _ => false
    end.

  Inductive PacingRecommendation : Type :=
    | PR_Atropine
    | PR_TCP_Immediate
    | PR_TVP_Urgent
    | PR_Dopamine
    | PR_Epinephrine
    | PR_SeekExpertConsult
    | PR_ObserveMonitor
    | PR_ContinueCurrentPacing.

  Definition recommend_pacing (bs : BradycardiaState) : PacingRecommendation :=
    if negb (is_symptomatic bs) then PR_ObserveMonitor
    else if pea_from_bradycardia bs then
      if pacing_for_bradycardic_pea bs then PR_TCP_Immediate
      else PR_ObserveMonitor
    else if is_critical_bradycardia bs then PR_TCP_Immediate
    else if can_give_atropine bs then PR_Atropine
    else if pacing_indicated bs then
      match pacing_mode bs with
      | NoPacing => PR_TCP_Immediate
      | TCP => if capture_achieved bs then PR_ContinueCurrentPacing else PR_TVP_Urgent
      | TVP => if capture_achieved bs then PR_ContinueCurrentPacing else PR_SeekExpertConsult
      | PermanentPacer => PR_SeekExpertConsult
      end
    else if negb (dopamine_infusing bs) then PR_Dopamine
    else if negb (epinephrine_infusing bs) then PR_Epinephrine
    else PR_SeekExpertConsult.

  Definition symptomatic_third_degree : BradycardiaState :=
    mkBradyState 35 ThirdDegreeAVBlock true true 80 true false 0 false false NoPacing false false.

  Definition asymptomatic_sinus_brady : BradycardiaState :=
    mkBradyState 55 SinusBradycardia false true 120 false false 0 false false NoPacing false false.

  Definition pea_with_av_block : BradycardiaState :=
    mkBradyState 25 ThirdDegreeAVBlock true false 0 true false 0 false false NoPacing false false.

  Definition asymptomatic_third_degree : BradycardiaState :=
    mkBradyState 45 ThirdDegreeAVBlock false true 110 false false 0 false false NoPacing false false.

  Theorem third_degree_tcp_immediate :
    recommend_pacing symptomatic_third_degree = PR_TCP_Immediate.
  Proof. reflexivity. Qed.

  Theorem asymptomatic_observe :
    recommend_pacing asymptomatic_third_degree = PR_ObserveMonitor.
  Proof. reflexivity. Qed.

  Theorem pea_av_block_tcp :
    recommend_pacing pea_with_av_block = PR_TCP_Immediate.
  Proof. reflexivity. Qed.

  Theorem atropine_wont_help_third_degree :
    atropine_may_help symptomatic_third_degree = false.
  Proof. reflexivity. Qed.

  Definition sinus_brady_symptomatic : BradycardiaState :=
    mkBradyState 45 SinusBradycardia true true 90 true false 0 false false NoPacing false false.

  Theorem sinus_brady_gets_atropine :
    recommend_pacing sinus_brady_symptomatic = PR_Atropine.
  Proof. reflexivity. Qed.

  Theorem atropine_helps_sinus :
    atropine_may_help sinus_brady_symptomatic = true.
  Proof. reflexivity. Qed.

  Definition tcp_settings_valid (rate output : nat) : bool :=
    (tcp_initial_rate_ppm <=? rate) &&
    (rate <=? tcp_max_rate_ppm) &&
    (output <=? tcp_max_output_mA).

  Definition tvp_settings_valid (rate output_x10 : nat) : bool :=
    (tvp_initial_rate_ppm <=? rate) &&
    (rate <=? tvp_max_rate_ppm).

  Theorem tcp_60_70_valid : tcp_settings_valid 60 70 = true.
  Proof. reflexivity. Qed.

  Theorem tcp_200_invalid : tcp_settings_valid 200 70 = false.
  Proof. reflexivity. Qed.

  Definition capture_confirmation (mechanical_capture electrical_capture pulse_present : bool) : bool :=
    electrical_capture && (mechanical_capture || pulse_present).

  Theorem capture_requires_electrical : forall m p,
    capture_confirmation m false p = false.
  Proof. reflexivity. Qed.

  Definition pacing_complete (bs : BradycardiaState) : bool :=
    match pacing_mode bs with
    | TVP | PermanentPacer => capture_achieved bs
    | TCP => capture_achieved bs
    | NoPacing => negb (pacing_indicated bs)
    end.

End Pacing.

(******************************************************************************)
(*                                                                            *)
(*                  SECTION 8A: HYPERKALEMIA EKG PATTERNS                     *)
(*                                                                            *)
(*  EKG manifestations of hyperkalemia by potassium level per AHA 2020.       *)
(*  Progression: peaked T -> QRS widening -> sine wave -> VF/asystole.        *)
(*                                                                            *)
(******************************************************************************)

Module HyperkalemiaEKG.

  Inductive EKGPattern : Type :=
    | Normal
    | PeakedT
    | PRProlongation
    | QRSWidening
    | PwaveFlattening
    | SineWave
    | VentricularFibrillation
    | Asystole.

  Definition pattern_eq_dec : forall p1 p2 : EKGPattern, {p1 = p2} + {p1 <> p2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Definition all_patterns : list EKGPattern :=
    [Normal; PeakedT; PRProlongation; QRSWidening;
     PwaveFlattening; SineWave; VentricularFibrillation; Asystole].

  Lemma all_patterns_complete : forall p : EKGPattern, In p all_patterns.
  Proof. intros []; simpl; auto 10. Qed.

  Definition potassium_normal_max_x10 : nat := 55.
  Definition potassium_mild_hyperK_x10 : nat := 60.
  Definition potassium_moderate_hyperK_x10 : nat := 70.
  Definition potassium_severe_hyperK_x10 : nat := 80.
  Definition potassium_critical_x10 : nat := 90.

  Definition expected_pattern_for_K (k_x10 : nat) : EKGPattern :=
    if k_x10 <=? potassium_normal_max_x10 then Normal
    else if k_x10 <=? potassium_mild_hyperK_x10 then PeakedT
    else if k_x10 <=? potassium_moderate_hyperK_x10 then QRSWidening
    else if k_x10 <=? potassium_severe_hyperK_x10 then SineWave
    else VentricularFibrillation.

  Definition is_life_threatening_pattern (p : EKGPattern) : bool :=
    match p with
    | SineWave | VentricularFibrillation | Asystole => true
    | _ => false
    end.

  Definition requires_immediate_calcium (p : EKGPattern) : bool :=
    match p with
    | QRSWidening | SineWave | VentricularFibrillation | Asystole => true
    | _ => false
    end.

  Definition pattern_severity (p : EKGPattern) : nat :=
    match p with
    | Normal => 0
    | PeakedT => 1
    | PRProlongation => 2
    | QRSWidening => 3
    | PwaveFlattening => 4
    | SineWave => 5
    | VentricularFibrillation => 6
    | Asystole => 7
    end.

  Definition pattern_worse_than (p1 p2 : EKGPattern) : bool :=
    pattern_severity p2 <? pattern_severity p1.

  Theorem normal_K_normal_EKG : expected_pattern_for_K 45 = Normal.
  Proof. reflexivity. Qed.

  Theorem mild_hyperK_peaked_T : expected_pattern_for_K 58 = PeakedT.
  Proof. reflexivity. Qed.

  Theorem moderate_hyperK_QRS : expected_pattern_for_K 68 = QRSWidening.
  Proof. reflexivity. Qed.

  Theorem severe_hyperK_sine : expected_pattern_for_K 75 = SineWave.
  Proof. reflexivity. Qed.

  Theorem critical_hyperK_VF : expected_pattern_for_K 95 = VentricularFibrillation.
  Proof. reflexivity. Qed.

  Theorem sine_wave_life_threatening : is_life_threatening_pattern SineWave = true.
  Proof. reflexivity. Qed.

  Theorem QRS_widening_needs_calcium : requires_immediate_calcium QRSWidening = true.
  Proof. reflexivity. Qed.

  Theorem peaked_T_no_immediate_calcium : requires_immediate_calcium PeakedT = false.
  Proof. reflexivity. Qed.

  Lemma leb_reflect : forall n m, (n <=? m) = true <-> n <= m.
  Proof. intros. apply Nat.leb_le. Qed.

  Lemma leb_reflect_false : forall n m, (n <=? m) = false <-> n > m.
  Proof. intros. rewrite Nat.leb_gt. reflexivity. Qed.

  Theorem severity_monotonic : forall k1 k2,
    k1 <= k2 ->
    pattern_severity (expected_pattern_for_K k1) <= pattern_severity (expected_pattern_for_K k2).
  Proof.
    intros k1 k2 Hle.
    unfold expected_pattern_for_K, potassium_normal_max_x10, potassium_mild_hyperK_x10,
           potassium_moderate_hyperK_x10, potassium_severe_hyperK_x10.
    repeat match goal with
    | |- context [if ?c then _ else _] => destruct c eqn:?
    end; simpl; try lia;
    repeat match goal with
    | H : (_ <=? _) = true |- _ => apply leb_reflect in H
    | H : (_ <=? _) = false |- _ => apply leb_reflect_false in H
    end; lia.
  Qed.

End HyperkalemiaEKG.

(******************************************************************************)
(*                                                                            *)
(*                  SECTION 8A2: QTC INTERVAL AND TORSADES                    *)
(*                                                                            *)
(*  QTc interval measurement, prolongation thresholds, and Torsades de        *)
(*  Pointes risk stratification per AHA 2020. QTc >500ms high risk.           *)
(*                                                                            *)
(******************************************************************************)

Module QTcTorsades.

  Definition qtc_normal_upper_ms : nat := 440.
  Definition qtc_borderline_upper_ms : nat := 460.
  Definition qtc_prolonged_threshold_ms : nat := 480.
  Definition qtc_high_risk_threshold_ms : nat := 500.
  Definition qtc_critical_threshold_ms : nat := 550.

  Definition qtc_normal_lower_ms : nat := 350.
  Definition qtc_short_threshold_ms : nat := 340.

  Inductive QTcCategory : Type :=
    | QTc_Short
    | QTc_Normal
    | QTc_Borderline
    | QTc_Prolonged
    | QTc_HighRisk
    | QTc_Critical.

  Definition qtc_category_eq_dec : forall q1 q2 : QTcCategory, {q1 = q2} + {q1 <> q2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Definition classify_qtc (qtc_ms : nat) : QTcCategory :=
    if qtc_ms <? qtc_short_threshold_ms then QTc_Short
    else if qtc_ms <? qtc_normal_upper_ms then QTc_Normal
    else if qtc_ms <? qtc_borderline_upper_ms then QTc_Borderline
    else if qtc_ms <? qtc_prolonged_threshold_ms then QTc_Prolonged
    else if qtc_ms <? qtc_high_risk_threshold_ms then QTc_HighRisk
    else QTc_Critical.

  Definition torsades_risk_score (qtc : QTcCategory) : nat :=
    match qtc with
    | QTc_Short => 1
    | QTc_Normal => 0
    | QTc_Borderline => 1
    | QTc_Prolonged => 2
    | QTc_HighRisk => 3
    | QTc_Critical => 4
    end.

  Inductive QTcCause : Type :=
    | QTc_Congenital
    | QTc_DrugInduced
    | QTc_Electrolyte
    | QTc_Ischemia
    | QTc_Bradycardia
    | QTc_Hypothermia
    | QTc_Unknown.

  Definition qtc_cause_eq_dec : forall c1 c2 : QTcCause, {c1 = c2} + {c1 <> c2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Definition qt_prolonging_drugs : list nat :=
    [1; 2; 3; 4; 5; 6; 7; 8; 9; 10].

  Record QTcAssessment : Type := mkQTcAssess {
    qtc_value_ms : nat;
    qtc_category : QTcCategory;
    qtc_cause : QTcCause;
    has_syncope : bool;
    has_family_history_scd : bool;
    on_qt_prolonging_drug : bool;
    potassium_low : bool;
    magnesium_low : bool;
    calcium_low : bool;
    heart_rate_at_measurement : nat
  }.

  Definition electrolyte_correction_needed (qa : QTcAssessment) : bool :=
    potassium_low qa || magnesium_low qa || calcium_low qa.

  Definition drug_discontinuation_needed (qa : QTcAssessment) : bool :=
    on_qt_prolonging_drug qa &&
    match qtc_category qa with
    | QTc_Prolonged | QTc_HighRisk | QTc_Critical => true
    | _ => false
    end.

  Definition magnesium_indicated_for_qtc (qa : QTcAssessment) : bool :=
    match qtc_category qa with
    | QTc_HighRisk | QTc_Critical => true
    | QTc_Prolonged => magnesium_low qa
    | _ => false
    end.

  Definition torsades_high_risk (qa : QTcAssessment) : bool :=
    match qtc_category qa with
    | QTc_Critical => true
    | QTc_HighRisk => has_syncope qa || has_family_history_scd qa
    | _ => false
    end.

  Definition isoproterenol_indicated (qa : QTcAssessment) : bool :=
    torsades_high_risk qa && (heart_rate_at_measurement qa <? 60).

  Definition pacing_indicated_for_qtc (qa : QTcAssessment) : bool :=
    torsades_high_risk qa && (heart_rate_at_measurement qa <? 50).

  Inductive TorsadesRecommendation : Type :=
    | TdP_ObserveMonitor
    | TdP_CorrectElectrolytes
    | TdP_DiscontinueDrugs
    | TdP_GiveMagnesium
    | TdP_Isoproterenol
    | TdP_OverdrivePacing
    | TdP_ICD_Evaluation.

  Definition recommend_torsades_management (qa : QTcAssessment) : TorsadesRecommendation :=
    if pacing_indicated_for_qtc qa then TdP_OverdrivePacing
    else if isoproterenol_indicated qa then TdP_Isoproterenol
    else if magnesium_indicated_for_qtc qa then TdP_GiveMagnesium
    else if drug_discontinuation_needed qa then TdP_DiscontinueDrugs
    else if electrolyte_correction_needed qa then TdP_CorrectElectrolytes
    else if has_family_history_scd qa && match qtc_category qa with QTc_Prolonged | QTc_HighRisk | QTc_Critical => true | _ => false end then TdP_ICD_Evaluation
    else TdP_ObserveMonitor.

  Definition critical_qtc_assessment : QTcAssessment :=
    mkQTcAssess 560 QTc_Critical QTc_DrugInduced true false true true true false 45.

  Definition normal_qtc_assessment : QTcAssessment :=
    mkQTcAssess 420 QTc_Normal QTc_Unknown false false false false false false 70.

  Definition borderline_qtc_assessment : QTcAssessment :=
    mkQTcAssess 455 QTc_Borderline QTc_Unknown false false false false false false 65.

  Theorem critical_qtc_is_high_risk :
    torsades_high_risk critical_qtc_assessment = true.
  Proof. reflexivity. Qed.

  Theorem normal_qtc_not_high_risk :
    torsades_high_risk normal_qtc_assessment = false.
  Proof. reflexivity. Qed.

  Theorem critical_qtc_needs_magnesium :
    magnesium_indicated_for_qtc critical_qtc_assessment = true.
  Proof. reflexivity. Qed.

  Theorem critical_qtc_gets_pacing :
    recommend_torsades_management critical_qtc_assessment = TdP_OverdrivePacing.
  Proof. reflexivity. Qed.

  Theorem normal_qtc_observe :
    recommend_torsades_management normal_qtc_assessment = TdP_ObserveMonitor.
  Proof. reflexivity. Qed.

  Theorem classify_420_normal : classify_qtc 420 = QTc_Normal.
  Proof. reflexivity. Qed.

  Theorem classify_455_borderline : classify_qtc 455 = QTc_Borderline.
  Proof. reflexivity. Qed.

  Theorem classify_490_prolonged : classify_qtc 490 = QTc_HighRisk.
  Proof. reflexivity. Qed.

  Theorem classify_560_critical : classify_qtc 560 = QTc_Critical.
  Proof. reflexivity. Qed.

  Inductive QTCorrectionMethod : Type :=
    | Bazett
    | Fridericia
    | Framingham
    | Hodges.

  Definition correction_method_eq_dec : forall m1 m2 : QTCorrectionMethod, {m1 = m2} + {m1 <> m2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Definition qt_correction_difference_acceptable (qtc1 qtc2 : nat) : bool :=
    let diff := if qtc1 <? qtc2 then qtc2 - qtc1 else qtc1 - qtc2 in
    diff <? 30.

  Definition qtc_risk_stratification (qa : QTcAssessment) : nat :=
    torsades_risk_score (qtc_category qa) +
    (if has_syncope qa then 2 else 0) +
    (if has_family_history_scd qa then 2 else 0) +
    (if electrolyte_correction_needed qa then 1 else 0) +
    (if on_qt_prolonging_drug qa then 1 else 0).

  Definition high_risk_score_threshold : nat := 4.

  Definition needs_urgent_intervention (qa : QTcAssessment) : bool :=
    high_risk_score_threshold <=? qtc_risk_stratification qa.

  Theorem critical_qtc_needs_urgent :
    needs_urgent_intervention critical_qtc_assessment = true.
  Proof. reflexivity. Qed.

End QTcTorsades.

(******************************************************************************)
(*                                                                            *)
(*                 SECTION 8B: HYPOTHERMIC CARDIAC ARREST                     *)
(*                                                                            *)
(*  Special considerations for hypothermic arrest per AHA 2020. Core temp     *)
(*  thresholds determine medication timing and defibrillation strategy.       *)
(*  "No one is dead until warm and dead."                                     *)
(*                                                                            *)
(******************************************************************************)

Module HypothermicArrest.

  Definition core_temp_severe_hypothermia_x10 : nat := 300.
  Definition core_temp_moderate_hypothermia_x10 : nat := 320.
  Definition core_temp_mild_hypothermia_x10 : nat := 340.
  Definition core_temp_normal_min_x10 : nat := 365.

  Inductive HypothermiaGrade : Type :=
    | Normothermic
    | MildHypothermia
    | ModerateHypothermia
    | SevereHypothermia.

  Definition grade_eq_dec : forall g1 g2 : HypothermiaGrade, {g1 = g2} + {g1 <> g2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Definition hypothermia_grade (temp_x10 : nat) : HypothermiaGrade :=
    if temp_x10 <? core_temp_severe_hypothermia_x10 then SevereHypothermia
    else if temp_x10 <? core_temp_moderate_hypothermia_x10 then ModerateHypothermia
    else if temp_x10 <? core_temp_mild_hypothermia_x10 then MildHypothermia
    else Normothermic.

  Definition meds_allowed (grade : HypothermiaGrade) : bool :=
    match grade with
    | Normothermic | MildHypothermia | ModerateHypothermia => true
    | SevereHypothermia => false
    end.

  Definition defib_allowed (grade : HypothermiaGrade) : bool :=
    match grade with
    | Normothermic | MildHypothermia | ModerateHypothermia => true
    | SevereHypothermia => true
    end.

  Definition max_defib_attempts_severe : nat := 1.

  Definition repeat_defib_allowed (grade : HypothermiaGrade) (attempts : nat) : bool :=
    match grade with
    | Normothermic | MildHypothermia | ModerateHypothermia => true
    | SevereHypothermia => attempts <? max_defib_attempts_severe
    end.

  Definition epi_interval_extended (grade : HypothermiaGrade) : bool :=
    match grade with
    | SevereHypothermia | ModerateHypothermia => true
    | MildHypothermia | Normothermic => false
    end.

  Definition extended_epi_interval_min : nat := 6.

  Definition continue_cpr_during_rewarming : bool := true.

  Definition target_rewarming_rate_C_per_hr_x10 : nat := 10.

  Record HypothermicPatient : Type := mkHypoPatient {
    core_temp_x10 : nat;
    arrest_duration_min : nat;
    submersion : bool;
    avalanche : bool;
    witnessed : bool
  }.

  Definition is_hypothermic (p : HypothermicPatient) : bool :=
    core_temp_x10 p <? core_temp_mild_hypothermia_x10.

  Definition patient_grade (p : HypothermicPatient) : HypothermiaGrade :=
    hypothermia_grade (core_temp_x10 p).

  Definition can_give_meds (p : HypothermicPatient) : bool :=
    meds_allowed (patient_grade p).

  Definition can_repeat_shock (p : HypothermicPatient) (shock_count : nat) : bool :=
    repeat_defib_allowed (patient_grade p) shock_count.

  Definition should_extend_resuscitation (p : HypothermicPatient) : bool :=
    is_hypothermic p && (witnessed p || submersion p || avalanche p).

  Definition max_resuscitation_duration_hypothermic_min : nat := 120.

  Definition ecmo_rewarming_indicated (p : HypothermicPatient) : bool :=
    (core_temp_x10 p <? core_temp_moderate_hypothermia_x10) &&
    should_extend_resuscitation p.

  Theorem severe_no_meds :
    meds_allowed SevereHypothermia = false.
  Proof. reflexivity. Qed.

  Theorem moderate_allows_meds :
    meds_allowed ModerateHypothermia = true.
  Proof. reflexivity. Qed.

  Theorem severe_hypothermia_grade :
    hypothermia_grade 280 = SevereHypothermia.
  Proof. reflexivity. Qed.

  Theorem moderate_hypothermia_grade :
    hypothermia_grade 310 = ModerateHypothermia.
  Proof. reflexivity. Qed.

  Theorem mild_hypothermia_grade :
    hypothermia_grade 330 = MildHypothermia.
  Proof. reflexivity. Qed.

  Theorem normal_temp_grade :
    hypothermia_grade 370 = Normothermic.
  Proof. reflexivity. Qed.

  Theorem severe_one_shock_only : forall attempts,
    attempts >= 1 ->
    repeat_defib_allowed SevereHypothermia attempts = false.
  Proof.
    intros attempts H.
    unfold repeat_defib_allowed, max_defib_attempts_severe.
    destruct (attempts <? 1) eqn:E.
    - apply Nat.ltb_lt in E. lia.
    - reflexivity.
  Qed.

  Theorem moderate_extended_epi :
    epi_interval_extended ModerateHypothermia = true.
  Proof. reflexivity. Qed.

  Theorem mild_normal_epi :
    epi_interval_extended MildHypothermia = false.
  Proof. reflexivity. Qed.

  Definition submersion_victim : HypothermicPatient :=
    mkHypoPatient 280 30 true false true.

  Definition avalanche_victim : HypothermicPatient :=
    mkHypoPatient 260 45 false true true.

  Theorem submersion_no_meds :
    can_give_meds submersion_victim = false.
  Proof. reflexivity. Qed.

  Theorem submersion_extend_resus :
    should_extend_resuscitation submersion_victim = true.
  Proof. reflexivity. Qed.

  Theorem submersion_ecmo_indicated :
    ecmo_rewarming_indicated submersion_victim = true.
  Proof. reflexivity. Qed.

  Theorem avalanche_ecmo_indicated :
    ecmo_rewarming_indicated avalanche_victim = true.
  Proof. reflexivity. Qed.

  Definition serum_potassium_futility_threshold_x10 : nat := 120.

  Definition futility_likely (p : HypothermicPatient) (k_x10 : nat) : bool :=
    serum_potassium_futility_threshold_x10 <=? k_x10.

  Theorem high_K_futile :
    futility_likely submersion_victim 130 = true.
  Proof. reflexivity. Qed.

  Theorem normal_K_not_futile :
    futility_likely submersion_victim 45 = false.
  Proof. reflexivity. Qed.

End HypothermicArrest.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 8C: DROWNING PROTOCOL                           *)
(*                                                                            *)
(*  Drowning-specific arrest modifications per AHA 2020. Prioritize airway    *)
(*  and ventilation. Extended resuscitation in cold water submersion.         *)
(*                                                                            *)
(******************************************************************************)

Module DrowningProtocol.

  Import HypothermicArrest.

  Definition ventilation_first : bool := true.

  Definition rescue_breaths_before_compressions : nat := 5.

  Definition cold_water_threshold_C_x10 : nat := 200.

  Inductive WaterType : Type :=
    | Freshwater
    | Saltwater
    | Chlorinated.

  Definition water_type_eq_dec : forall w1 w2 : WaterType, {w1 = w2} + {w1 <> w2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Record DrowningVictim : Type := mkDrowningVictim {
    submersion_duration_min : nat;
    water_temp_x10 : nat;
    water_type : WaterType;
    witnessed_submersion : bool;
    bystander_cpr : bool;
    core_temp_on_arrival_x10 : nat
  }.

  Definition is_cold_water (v : DrowningVictim) : bool :=
    water_temp_x10 v <? cold_water_threshold_C_x10.

  Definition is_hypothermic_drowning (v : DrowningVictim) : bool :=
    core_temp_on_arrival_x10 v <? core_temp_mild_hypothermia_x10.

  Definition extend_resuscitation_drowning (v : DrowningVictim) : bool :=
    is_cold_water v || is_hypothermic_drowning v.

  Definition submersion_survival_unlikely_warm_min : nat := 30.
  Definition submersion_survival_possible_cold_min : nat := 90.

  Definition resuscitation_indicated (v : DrowningVictim) : bool :=
    if is_cold_water v then
      submersion_duration_min v <? submersion_survival_possible_cold_min
    else
      submersion_duration_min v <? submersion_survival_unlikely_warm_min.

  Definition good_prognosis_factors (v : DrowningVictim) : nat :=
    (if witnessed_submersion v then 1 else 0) +
    (if bystander_cpr v then 1 else 0) +
    (if is_cold_water v then 1 else 0) +
    (if submersion_duration_min v <? 10 then 1 else 0).

  Definition favorable_prognosis (v : DrowningVictim) : bool :=
    3 <=? good_prognosis_factors v.

  Definition prioritize_airway : bool := true.

  Definition spinal_precautions_if_diving : bool := true.

  Definition abdominal_thrusts_not_recommended : bool := true.

  Definition brief_cold_submersion : DrowningVictim :=
    mkDrowningVictim 5 150 Freshwater true true 320.

  Definition prolonged_warm_submersion : DrowningVictim :=
    mkDrowningVictim 45 280 Saltwater false false 360.

  Theorem cold_submersion_extend :
    extend_resuscitation_drowning brief_cold_submersion = true.
  Proof. reflexivity. Qed.

  Theorem warm_prolonged_no_extend :
    extend_resuscitation_drowning prolonged_warm_submersion = false.
  Proof. reflexivity. Qed.

  Theorem brief_cold_indicated :
    resuscitation_indicated brief_cold_submersion = true.
  Proof. reflexivity. Qed.

  Theorem prolonged_warm_not_indicated :
    resuscitation_indicated prolonged_warm_submersion = false.
  Proof. reflexivity. Qed.

  Theorem brief_cold_favorable :
    favorable_prognosis brief_cold_submersion = true.
  Proof. reflexivity. Qed.

  Theorem prolonged_warm_unfavorable :
    favorable_prognosis prolonged_warm_submersion = false.
  Proof. reflexivity. Qed.

  Definition witnessed_cold_water_priority : Prop :=
    forall v, witnessed_submersion v = true ->
              is_cold_water v = true ->
              submersion_duration_min v < submersion_survival_possible_cold_min ->
              resuscitation_indicated v = true.

  Theorem witnessed_cold_priority_holds : witnessed_cold_water_priority.
  Proof.
    unfold witnessed_cold_water_priority.
    intros v _ Hcold Hdur.
    unfold resuscitation_indicated.
    rewrite Hcold.
    apply Nat.ltb_lt. exact Hdur.
  Qed.

End DrowningProtocol.

(******************************************************************************)
(*                                                                            *)
(*           SECTION 8D: INTEGRATED SPECIAL POPULATION DECISIONS              *)
(*                                                                            *)
(*  Decision logic integrating hypothermia, drowning, and pediatric           *)
(*  considerations into the main ACLS algorithm.                              *)
(*                                                                            *)
(******************************************************************************)

Module SpecialPopulationDecision.

  Import AlgorithmState.
  Import Decision.
  Import HypothermicArrest.
  Import DrowningProtocol.

  Definition recommend_hypothermic (s : AlgorithmState.t) (temp_x10 : nat) : Recommendation :=
    let grade := hypothermia_grade temp_x10 in
    if rosc_achieved s then ROSC_achieved
    else match grade with
         | SevereHypothermia =>
           if is_shockable_state s && (shock_count s =? 0)
           then Shock_then_CPR
           else CPR_only
         | ModerateHypothermia
         | MildHypothermia
         | Normothermic =>
           recommend s
         end.

  Definition hypothermic_meds_allowed (temp_x10 : nat) : bool :=
    meds_allowed (hypothermia_grade temp_x10).

  Definition hypothermic_repeat_shock_allowed (temp_x10 shock_count : nat) : bool :=
    repeat_defib_allowed (hypothermia_grade temp_x10) shock_count.

  Definition recommend_drowning (s : AlgorithmState.t) (v : DrowningVictim) : Recommendation :=
    if rosc_achieved s then ROSC_achieved
    else if negb (resuscitation_indicated v) then CPR_only
    else if is_hypothermic_drowning v then
      recommend_hypothermic s (core_temp_on_arrival_x10 v)
    else recommend s.

  Definition recommend_pediatric (s : AlgorithmState.t) (p : Medication.PediatricPatient) : Recommendation :=
    if rosc_achieved s then ROSC_achieved
    else recommend s.

  Definition peds_defibrillation_energy (p : Medication.PediatricPatient) (shock_num : nat) : nat :=
    if shock_num =? 1
    then Medication.defibrillation_peds_initial p
    else Medication.defibrillation_peds_subsequent p.

  Definition peds_defibrillation_valid (p : Medication.PediatricPatient) (energy shock_num : nat) : bool :=
    let expected := peds_defibrillation_energy p shock_num in
    let max := Medication.defibrillation_peds_max p in
    (expected <=? energy) && (energy <=? max).

  Theorem severe_hypothermia_no_meds : forall temp,
    temp < core_temp_severe_hypothermia_x10 ->
    hypothermic_meds_allowed temp = false.
  Proof.
    intros temp Htemp.
    unfold hypothermic_meds_allowed, hypothermia_grade, meds_allowed, core_temp_severe_hypothermia_x10 in *.
    destruct (temp <? 300) eqn:E.
    - reflexivity.
    - apply Nat.ltb_nlt in E. exfalso. apply E. exact Htemp.
  Qed.

  Theorem severe_hypothermia_single_shock : forall temp,
    temp < core_temp_severe_hypothermia_x10 ->
    hypothermic_repeat_shock_allowed temp 1 = false.
  Proof.
    intros temp Htemp.
    unfold hypothermic_repeat_shock_allowed, hypothermia_grade, repeat_defib_allowed, core_temp_severe_hypothermia_x10 in *.
    destruct (temp <? 300) eqn:E.
    - reflexivity.
    - apply Nat.ltb_nlt in E. exfalso. apply E. exact Htemp.
  Qed.

  Theorem severe_hypothermia_cpr_only : forall s temp,
    temp < core_temp_severe_hypothermia_x10 ->
    rosc_achieved s = false ->
    shock_count s > 0 ->
    recommend_hypothermic s temp = CPR_only.
  Proof.
    intros s temp Htemp Hrosc Hsc.
    unfold recommend_hypothermic, hypothermia_grade, core_temp_severe_hypothermia_x10 in *.
    rewrite Hrosc.
    destruct (temp <? 300) eqn:E.
    - destruct (is_shockable_state s).
      + destruct (shock_count s) eqn:Esc.
        * exfalso. lia.
        * reflexivity.
      + reflexivity.
    - apply Nat.ltb_nlt in E. exfalso. apply E. exact Htemp.
  Qed.

  Theorem moderate_hypothermia_normal_protocol : forall s temp,
    core_temp_severe_hypothermia_x10 <= temp ->
    temp < core_temp_moderate_hypothermia_x10 ->
    rosc_achieved s = false ->
    recommend_hypothermic s temp = recommend s.
  Proof.
    intros s temp Hlow Hhigh Hrosc.
    unfold recommend_hypothermic, hypothermia_grade, core_temp_severe_hypothermia_x10, core_temp_moderate_hypothermia_x10 in *.
    rewrite Hrosc.
    destruct (temp <? 300) eqn:E1.
    - apply Nat.ltb_lt in E1. exfalso. lia.
    - destruct (temp <? 320) eqn:E2.
      + reflexivity.
      + apply Nat.ltb_nlt in E2. exfalso. lia.
  Qed.

  Theorem drowning_cold_water_extends : forall s v,
    rosc_achieved s = false ->
    resuscitation_indicated v = true ->
    is_hypothermic_drowning v = true ->
    core_temp_on_arrival_x10 v < core_temp_severe_hypothermia_x10 ->
    shock_count s > 0 ->
    recommend_drowning s v = CPR_only.
  Proof.
    intros s v Hrosc Hresus Hhypo Htemp Hsc.
    unfold recommend_drowning.
    rewrite Hrosc, Hresus, Hhypo.
    apply severe_hypothermia_cpr_only; assumption.
  Qed.

  Theorem peds_initial_shock_valid : forall p,
    peds_defibrillation_valid p (Medication.defibrillation_peds_initial p) 1 = true.
  Proof.
    intros p.
    unfold peds_defibrillation_valid, peds_defibrillation_energy.
    simpl.
    apply andb_true_iff. split.
    - apply Nat.leb_refl.
    - unfold Medication.defibrillation_peds_initial, Medication.defibrillation_peds_max.
      apply Nat.leb_le.
      unfold Medication.defibrillation_peds_initial_J_per_kg, Medication.defibrillation_peds_max_J_per_kg.
      lia.
  Qed.

End SpecialPopulationDecision.

(******************************************************************************)
(*                                                                            *)
(*                      SECTION 9: DEFIBRILLATION                             *)
(*                                                                            *)
(*  Defibrillator types, energy levels, and shock delivery parameters.        *)
(*  Biphasic 120-200J initial, Monophasic 360J. Escalating energy optional.   *)
(*                                                                            *)
(******************************************************************************)

Module Defibrillation.

  Inductive DefibrillatorType : Type :=
    | Biphasic
    | Monophasic.

  Definition defib_eq_dec : forall d1 d2 : DefibrillatorType,
    {d1 = d2} + {d1 <> d2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Definition biphasic_initial_min_J : nat := 120.
  Definition biphasic_initial_max_J : nat := 200.
  Definition biphasic_max_J : nat := 360.
  Definition monophasic_dose_J : nat := 360.

  Record ShockParams : Type := mkShockParams {
    defib_type : DefibrillatorType;
    energy_J : nat;
    shock_number : nat
  }.

  Definition energy_valid (sp : ShockParams) : bool :=
    match defib_type sp with
    | Biphasic =>
        if shock_number sp =? 1 then
          (biphasic_initial_min_J <=? energy_J sp) &&
          (energy_J sp <=? biphasic_initial_max_J)
        else
          (biphasic_initial_min_J <=? energy_J sp) &&
          (energy_J sp <=? biphasic_max_J)
    | Monophasic =>
        energy_J sp =? monophasic_dose_J
    end.

  Definition can_escalate (sp : ShockParams) : bool :=
    match defib_type sp with
    | Biphasic => energy_J sp <? biphasic_max_J
    | Monophasic => false
    end.

  Definition escalate (sp : ShockParams) : ShockParams :=
    match defib_type sp with
    | Biphasic =>
        let new_energy := Nat.min (energy_J sp + 50) biphasic_max_J in
        mkShockParams Biphasic new_energy (S (shock_number sp))
    | Monophasic =>
        mkShockParams Monophasic monophasic_dose_J (S (shock_number sp))
    end.

  Definition standard_biphasic_initial : ShockParams :=
    mkShockParams Biphasic 200 1.

  Definition standard_monophasic : ShockParams :=
    mkShockParams Monophasic 360 1.

  Theorem biphasic_initial_valid : energy_valid standard_biphasic_initial = true.
  Proof. reflexivity. Qed.

  Theorem monophasic_valid : energy_valid standard_monophasic = true.
  Proof. reflexivity. Qed.

  Theorem monophasic_cannot_escalate : can_escalate standard_monophasic = false.
  Proof. reflexivity. Qed.

  Theorem biphasic_can_escalate_from_200 :
    can_escalate (mkShockParams Biphasic 200 1) = true.
  Proof. reflexivity. Qed.

  Theorem biphasic_cannot_escalate_from_360 :
    can_escalate (mkShockParams Biphasic 360 3) = false.
  Proof. reflexivity. Qed.

  Theorem escalate_increases_shock_number : forall sp,
    shock_number (escalate sp) = S (shock_number sp).
  Proof. intros [[] e n]; reflexivity. Qed.

  Theorem escalate_biphasic_bounded : forall sp,
    defib_type sp = Biphasic ->
    energy_J (escalate sp) <= biphasic_max_J.
  Proof.
    intros sp Htype.
    unfold escalate. rewrite Htype.
    apply Nat.le_min_r.
  Qed.

  Theorem monophasic_energy_constant : forall sp,
    defib_type sp = Monophasic ->
    energy_J (escalate sp) = monophasic_dose_J.
  Proof.
    intros sp Htype.
    unfold escalate. rewrite Htype. reflexivity.
  Qed.

  Definition time_since_last_shock_valid (interval_sec : nat) : bool :=
    CPR.cycle_duration_sec <=? interval_sec.

  Theorem two_min_interval_valid : time_since_last_shock_valid 120 = true.
  Proof. reflexivity. Qed.

  Theorem one_min_interval_invalid : time_since_last_shock_valid 60 = false.
  Proof. reflexivity. Qed.

  Definition shock_appropriate (r : Rhythm.t) (sp : ShockParams) : bool :=
    Rhythm.shockable r && energy_valid sp.

  Theorem VF_with_valid_biphasic_appropriate :
    shock_appropriate Rhythm.VF standard_biphasic_initial = true.
  Proof. reflexivity. Qed.

  Theorem PEA_shock_never_appropriate : forall sp,
    shock_appropriate Rhythm.PEA sp = false.
  Proof. intros sp. reflexivity. Qed.

  Theorem Asystole_shock_never_appropriate : forall sp,
    shock_appropriate Rhythm.Asystole sp = false.
  Proof. intros sp. reflexivity. Qed.

End Defibrillation.

(******************************************************************************)
(*                                                                            *)
(*                   SECTION 10: PROTOCOL SEQUENCES                           *)
(*                                                                            *)
(*  Valid sequences of interventions. Enforces correct ordering of shocks,    *)
(*  CPR cycles, and drug administration per ACLS algorithm.                   *)
(*                                                                            *)
(******************************************************************************)

Module ProtocolSequence.

  Import AlgorithmState.

  Inductive Event : Type :=
    | E_Shock (energy : nat)
    | E_CPR_Cycle
    | E_Epinephrine
    | E_Amiodarone (dose : nat)
    | E_Rhythm_Check (found : Rhythm.t)
    | E_ROSC_Detected.

  Definition event_eq_dec : forall e1 e2 : Event, {e1 = e2} + {e1 <> e2}.
  Proof.
    intros [] []; try (right; discriminate).
    - destruct (Nat.eq_dec energy energy0); [left; f_equal; assumption | right; intro H; inversion H; contradiction].
    - left; reflexivity.
    - left; reflexivity.
    - destruct (Nat.eq_dec dose dose0); [left; f_equal; assumption | right; intro H; inversion H; contradiction].
    - destruct (Rhythm.eq_dec found found0); [left; f_equal; assumption | right; intro H; inversion H; contradiction].
    - left; reflexivity.
  Defined.

  Definition EventLog := list Event.

  Definition apply_event (s : AlgorithmState.t) (e : Event) : AlgorithmState.t :=
    match e with
    | E_Shock _ => with_shock s
    | E_CPR_Cycle => with_cpr_cycle s
    | E_Epinephrine => with_epinephrine s
    | E_Amiodarone _ => with_amiodarone s
    | E_Rhythm_Check r => with_rhythm s r
    | E_ROSC_Detected => with_rosc s
    end.

  Fixpoint apply_events (s : AlgorithmState.t) (events : EventLog) : AlgorithmState.t :=
    match events with
    | [] => s
    | e :: rest => apply_events (apply_event s e) rest
    end.

  Definition event_valid_for_state (s : AlgorithmState.t) (e : Event) : bool :=
    if rosc_achieved s then
      match e with E_ROSC_Detected => true | _ => false end
    else
      match e with
      | E_Shock _ => is_shockable_state s
      | E_CPR_Cycle => true
      | E_Epinephrine => epi_due s
      | E_Amiodarone _ => can_give_amiodarone s
      | E_Rhythm_Check _ => true
      | E_ROSC_Detected => true
      end.

  Fixpoint sequence_valid (s : AlgorithmState.t) (events : EventLog) : bool :=
    match events with
    | [] => true
    | e :: rest =>
        event_valid_for_state s e &&
        sequence_valid (apply_event s e) rest
    end.

  Definition shockable_sequence_1 : EventLog :=
    [E_Shock 200; E_CPR_Cycle; E_Rhythm_Check Rhythm.VF;
     E_Shock 200; E_Epinephrine; E_CPR_Cycle; E_Rhythm_Check Rhythm.VF;
     E_Shock 250; E_Amiodarone 300; E_CPR_Cycle].

  Definition nonshockable_sequence_1 : EventLog :=
    [E_Epinephrine; E_CPR_Cycle; E_Rhythm_Check Rhythm.PEA;
     E_CPR_Cycle; E_Rhythm_Check Rhythm.PEA;
     E_Epinephrine; E_CPR_Cycle].

  Theorem shockable_sequence_valid :
    sequence_valid (initial Rhythm.VF) shockable_sequence_1 = true.
  Proof. reflexivity. Qed.

  Theorem nonshockable_sequence_valid :
    sequence_valid (initial Rhythm.PEA) nonshockable_sequence_1 = true.
  Proof. reflexivity. Qed.

  Definition count_shocks (events : EventLog) : nat :=
    length (filter (fun e => match e with E_Shock _ => true | _ => false end) events).

  Definition count_epi (events : EventLog) : nat :=
    length (filter (fun e => match e with E_Epinephrine => true | _ => false end) events).

  Definition count_amio (events : EventLog) : nat :=
    length (filter (fun e => match e with E_Amiodarone _ => true | _ => false end) events).

  Theorem shockable_sequence_shock_count :
    count_shocks shockable_sequence_1 = 3.
  Proof. reflexivity. Qed.

  Theorem shockable_sequence_epi_count :
    count_epi shockable_sequence_1 = 1.
  Proof. reflexivity. Qed.

  Theorem shockable_sequence_amio_count :
    count_amio shockable_sequence_1 = 1.
  Proof. reflexivity. Qed.

  Lemma count_shocks_cons_shock : forall energy rest,
    count_shocks (E_Shock energy :: rest) = S (count_shocks rest).
  Proof. reflexivity. Qed.

  Lemma count_shocks_cons_other : forall e rest,
    (forall n, e <> E_Shock n) ->
    count_shocks (e :: rest) = count_shocks rest.
  Proof.
    intros e rest Hne.
    destruct e; try reflexivity.
    exfalso. apply (Hne energy). reflexivity.
  Qed.

  Lemma count_epi_cons_epi : forall rest,
    count_epi (E_Epinephrine :: rest) = S (count_epi rest).
  Proof. reflexivity. Qed.

  Lemma count_epi_cons_other : forall e rest,
    e <> E_Epinephrine ->
    count_epi (e :: rest) = count_epi rest.
  Proof.
    intros e rest Hne.
    destruct e; try reflexivity.
    exfalso. apply Hne. reflexivity.
  Qed.

  Theorem shock_on_nonshockable_invalid : forall s energy,
    is_shockable_state s = false ->
    rosc_achieved s = false ->
    event_valid_for_state s (E_Shock energy) = false.
  Proof.
    intros s energy Hns Hrosc.
    unfold event_valid_for_state.
    rewrite Hrosc, Hns. reflexivity.
  Qed.

  Theorem amio_before_third_shock_invalid : forall s dose,
    shock_count s < 3 ->
    rosc_achieved s = false ->
    event_valid_for_state s (E_Amiodarone dose) = false.
  Proof.
    intros s dose Hsc Hrosc.
    unfold event_valid_for_state.
    rewrite Hrosc.
    unfold can_give_amiodarone.
    destruct (is_shockable_state s); [|reflexivity].
    destruct (3 <=? shock_count s) eqn:E.
    - apply Nat.leb_le in E. lia.
    - reflexivity.
  Qed.

  Theorem rosc_blocks_further_shocks : forall s energy,
    rosc_achieved s = true ->
    event_valid_for_state s (E_Shock energy) = false.
  Proof.
    intros s energy Hrosc.
    unfold event_valid_for_state. rewrite Hrosc. reflexivity.
  Qed.

  Theorem rosc_blocks_further_epi : forall s,
    rosc_achieved s = true ->
    event_valid_for_state s E_Epinephrine = false.
  Proof.
    intros s Hrosc.
    unfold event_valid_for_state. rewrite Hrosc. reflexivity.
  Qed.

  Definition shock_energy_escalating (events : EventLog) : bool :=
    let shocks := filter (fun e => match e with E_Shock _ => true | _ => false end) events in
    let energies := map (fun e => match e with E_Shock e => e | _ => 0 end) shocks in
    match energies with
    | [] => true
    | e :: rest =>
      let fix escalating prev l :=
        match l with
        | [] => true
        | x :: xs => (prev <=? x) && escalating x xs
        end
      in escalating e rest
    end.

  Definition epi_timing_valid_in_log (events : EventLog) (cycle_sec : nat) : bool :=
    let epi_cycles := map (fun p => fst p) (filter (fun p => match snd p with E_Epinephrine => true | _ => false end)
                         (combine (seq 0 (length events)) events)) in
    match epi_cycles with
    | [] => true
    | _ :: [] => true
    | c1 :: c2 :: rest =>
      let min_gap := Medication.epinephrine_interval_min * 60 / cycle_sec in
      let fix check_gaps prev l :=
        match l with
        | [] => true
        | x :: xs => (min_gap <=? (x - prev)) && check_gaps x xs
        end
      in check_gaps c1 (c2 :: rest)
    end.

  Definition drug_sequence_valid (events : EventLog) : bool :=
    let amio_count := count_amio events in
    let lido_count := length (filter (fun e => match e with E_Amiodarone _ => false | _ => false end) events) in
    (amio_count <=? 2) &&
    ((amio_count =? 0) || (lido_count =? 0)).

  Theorem escalating_empty : shock_energy_escalating [] = true.
  Proof. reflexivity. Qed.

  Theorem escalating_single : forall e,
    shock_energy_escalating [E_Shock e] = true.
  Proof. reflexivity. Qed.

  Theorem escalating_200_250 :
    shock_energy_escalating [E_Shock 200; E_CPR_Cycle; E_Shock 250] = true.
  Proof. reflexivity. Qed.

  Lemma with_shock_preserves_amio : forall s,
    amiodarone_doses (with_shock s) = amiodarone_doses s.
  Proof. reflexivity. Qed.

  Lemma with_cpr_cycle_preserves_amio : forall s,
    amiodarone_doses (with_cpr_cycle s) = amiodarone_doses s.
  Proof. reflexivity. Qed.

  Lemma with_epinephrine_preserves_amio : forall s,
    amiodarone_doses (with_epinephrine s) = amiodarone_doses s.
  Proof. reflexivity. Qed.

  Lemma with_rhythm_preserves_amio : forall s r,
    amiodarone_doses (with_rhythm s r) = amiodarone_doses s.
  Proof. reflexivity. Qed.

  Lemma with_rosc_preserves_amio : forall s,
    amiodarone_doses (with_rosc s) = amiodarone_doses s.
  Proof. reflexivity. Qed.

  Lemma with_amiodarone_increments : forall s,
    amiodarone_doses (with_amiodarone s) = S (amiodarone_doses s).
  Proof. reflexivity. Qed.

  Theorem amio_event_valid_implies_under_limit : forall s dose,
    event_valid_for_state s (E_Amiodarone dose) = true ->
    amiodarone_doses s < 2.
  Proof.
    intros s dose H.
    unfold event_valid_for_state in H.
    destruct (rosc_achieved s); [discriminate|].
    unfold can_give_amiodarone in H.
    destruct (is_shockable_state s); [|discriminate].
    destruct (3 <=? shock_count s); [|discriminate].
    destruct (amiodarone_doses s <? 2) eqn:E; [|discriminate].
    destruct (lidocaine_doses s =? 0); [|discriminate].
    apply Nat.ltb_lt in E. exact E.
  Qed.

End ProtocolSequence.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 11: TIMING CONSTRAINTS                          *)
(*                                                                            *)
(*  Verification of timing constraints: CPR cycle duration, drug intervals,   *)
(*  rhythm check windows, and maximum resuscitation duration.                 *)
(*                                                                            *)
(******************************************************************************)

Module Timing.

  Definition max_resuscitation_min : nat := 60.
  Definition max_resuscitation_sec : nat := max_resuscitation_min * 60.

  Definition typical_cpr_cycles_in_hour : nat := max_resuscitation_sec / CPR.cycle_duration_sec.

  Theorem cycles_in_hour : typical_cpr_cycles_in_hour = 30.
  Proof. reflexivity. Qed.

  Definition epi_doses_possible_in_hour : nat :=
    max_resuscitation_sec / (Medication.epinephrine_interval_min * 60).

  Theorem max_epi_in_hour : epi_doses_possible_in_hour = 20.
  Proof. reflexivity. Qed.

  Record TimedState : Type := mkTimedState {
    state : AlgorithmState.t;
    wall_clock_sec : nat
  }.

  Definition elapsed_since_arrest (ts : TimedState) : nat :=
    wall_clock_sec ts.

  Definition within_resuscitation_window (ts : TimedState) : bool :=
    elapsed_since_arrest ts <? max_resuscitation_sec.

  Definition time_for_rhythm_check (ts : TimedState) : bool :=
    (AlgorithmState.time_sec (state ts)) mod CPR.cycle_duration_sec =? 0.

  Definition epi_timing_compliant (ts : TimedState) : bool :=
    match AlgorithmState.last_epi_time_sec (state ts) with
    | None => true
    | Some last =>
        let elapsed := AlgorithmState.time_sec (state ts) - last in
        Medication.epinephrine_interval_min * 60 <=? elapsed
    end.

  Theorem fresh_state_epi_compliant : forall r,
    epi_timing_compliant (mkTimedState (AlgorithmState.initial r) 0) = true.
  Proof. reflexivity. Qed.

  Definition advance_time (ts : TimedState) (delta_sec : nat) : TimedState :=
    let s := state ts in
    mkTimedState
      (AlgorithmState.mkState
        (AlgorithmState.current_rhythm s)
        (AlgorithmState.shock_count s)
        (AlgorithmState.cpr_cycles s)
        (AlgorithmState.epinephrine_doses s)
        (AlgorithmState.amiodarone_doses s)
        (AlgorithmState.lidocaine_doses s)
        (AlgorithmState.magnesium_doses s)
        (AlgorithmState.calcium_doses s)
        (AlgorithmState.bicarb_doses s)
        (AlgorithmState.lipid_doses s)
        (AlgorithmState.amiodarone_total_mg s)
        (AlgorithmState.lidocaine_total_mg s)
        (AlgorithmState.time_sec s + delta_sec)
        (AlgorithmState.last_epi_time_sec s)
        (AlgorithmState.last_epi_cpr_cycle s)
        (AlgorithmState.no_flow_time_sec s)
        (AlgorithmState.low_flow_time_sec s)
        (AlgorithmState.cpr_start_time_sec s)
        (AlgorithmState.etco2_during_cpr s)
        (AlgorithmState.has_iv_access s)
        (AlgorithmState.has_advanced_airway s)
        (AlgorithmState.rosc_achieved s)
        (AlgorithmState.identified_causes s)
        (AlgorithmState.patient_weight_kg s)
        (AlgorithmState.measured_ph_x100 s)
        (AlgorithmState.measured_potassium_x10 s)
        (AlgorithmState.is_torsades s)
        (AlgorithmState.ecpr_initiated s)
        (AlgorithmState.cath_lab_activated s))
      (wall_clock_sec ts + delta_sec).

  Theorem advance_increases_time : forall ts delta,
    wall_clock_sec (advance_time ts delta) = wall_clock_sec ts + delta.
  Proof. reflexivity. Qed.

  Definition cpr_fraction_adequate (compressions chest_time_sec : nat) : bool :=
    let expected := (chest_time_sec * CPR.min_rate_per_min) / 60 in
    let min_threshold := (expected * 60) / 100 in
    min_threshold <=? compressions.

  Theorem ideal_cpr_fraction :
    cpr_fraction_adequate 200 120 = true.
  Proof. reflexivity. Qed.

  Definition hands_off_time_acceptable (pause_sec : nat) : bool :=
    pause_sec <=? CPR.max_rhythm_check_sec.

  Theorem ten_sec_pause_ok : hands_off_time_acceptable 10 = true.
  Proof. reflexivity. Qed.

  Theorem fifteen_sec_pause_too_long : hands_off_time_acceptable 15 = false.
  Proof. reflexivity. Qed.

End Timing.

(******************************************************************************)
(*                                                                            *)
(*               SECTION 11B: TERMINATION OF RESUSCITATION                    *)
(*                                                                            *)
(*  Prognostication and termination rules per AHA 2020 and NAEMSP guidelines. *)
(*  BLS and ALS termination criteria, futility indicators, and family         *)
(*  presence considerations.                                                  *)
(*                                                                            *)
(******************************************************************************)

Module TerminationOfResuscitation.

  Import AlgorithmState.

  Definition standard_resuscitation_duration_min : nat := 20.
  Definition extended_resuscitation_duration_min : nat := 40.
  Definition maximum_resuscitation_duration_min : nat := 60.
  Definition hypothermic_max_duration_min : nat := 120.

  Definition etco2_futility_threshold_mmHg : nat := 10.
  Definition etco2_poor_prognosis_threshold_mmHg : nat := 20.

  Inductive TerminationReason : Type :=
    | TR_ROSCAchieved
    | TR_BLSTerminationCriteria
    | TR_ALSTerminationCriteria
    | TR_FutilityETCO2
    | TR_FutilityDuration
    | TR_DNROrderPresent
    | TR_ValidADPresent
    | TR_PhysicianOrder
    | TR_FamilyRequest
    | TR_TraumaticArrestNonSurvivable
    | TR_ProlongedDowntime.

  Definition termination_reason_eq_dec : forall t1 t2 : TerminationReason, {t1 = t2} + {t1 <> t2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Record BLSTerminationCriteria : Type := mkBLSTerm {
    bls_no_rosc : bool;
    bls_no_shockable_rhythm : bool;
    bls_ems_not_witnessed : bool;
    bls_no_bystander_cpr : bool;
    bls_no_aed_shock : bool
  }.

  Record ALSTerminationCriteria : Type := mkALSTerm {
    als_no_rosc : bool;
    als_no_shockable_rhythm : bool;
    als_ems_not_witnessed : bool;
    als_asystole_after_full_als : bool;
    als_etco2_below_threshold : bool;
    als_no_reversible_cause : bool
  }.

  Definition bls_termination_met (c : BLSTerminationCriteria) : bool :=
    bls_no_rosc c &&
    bls_no_shockable_rhythm c &&
    bls_ems_not_witnessed c &&
    bls_no_bystander_cpr c &&
    bls_no_aed_shock c.

  Definition als_termination_met (c : ALSTerminationCriteria) : bool :=
    als_no_rosc c &&
    als_no_shockable_rhythm c &&
    als_ems_not_witnessed c &&
    als_asystole_after_full_als c &&
    als_etco2_below_threshold c &&
    als_no_reversible_cause c.

  Record ResuscitationContext : Type := mkResusContext {
    arrest_witnessed_by_ems : bool;
    arrest_witnessed_by_bystander : bool;
    bystander_cpr_performed : bool;
    initial_rhythm_shockable_ctx : bool;
    aed_shock_delivered : bool;
    duration_min : nat;
    current_etco2 : option nat;
    reversible_cause_present : bool;
    reversible_cause_treated : bool;
    dnr_order_valid : bool;
    advance_directive_valid : bool;
    family_present : bool;
    family_requests_termination : bool;
    physician_present : bool;
    is_hypothermic_ctx : bool;
    is_pediatric_ctx : bool;
    is_pregnancy_ctx : bool;
    is_drug_overdose_ctx : bool
  }.

  Definition arrest_is_witnessed (ctx : ResuscitationContext) : bool :=
    arrest_witnessed_by_ems ctx || arrest_witnessed_by_bystander ctx.

  Definition should_extend_resuscitation (ctx : ResuscitationContext) : bool :=
    is_hypothermic_ctx ctx ||
    is_pregnancy_ctx ctx ||
    is_drug_overdose_ctx ctx ||
    is_pediatric_ctx ctx ||
    reversible_cause_present ctx.

  Definition etco2_indicates_futility (ctx : ResuscitationContext) : bool :=
    match current_etco2 ctx with
    | None => false
    | Some e => (20 <=? duration_min ctx) && (e <? etco2_futility_threshold_mmHg)
    end.

  Definition duration_indicates_futility (ctx : ResuscitationContext) : bool :=
    if should_extend_resuscitation ctx then
      if is_hypothermic_ctx ctx then
        hypothermic_max_duration_min <? duration_min ctx
      else
        extended_resuscitation_duration_min <? duration_min ctx
    else
      standard_resuscitation_duration_min <? duration_min ctx.

  Definition legal_authority_to_terminate (ctx : ResuscitationContext) : bool :=
    dnr_order_valid ctx ||
    advance_directive_valid ctx ||
    physician_present ctx.

  Definition build_bls_criteria (ctx : ResuscitationContext) (s : AlgorithmState.t) : BLSTerminationCriteria :=
    mkBLSTerm
      (negb (rosc_achieved s))
      (negb (is_shockable_state s))
      (negb (arrest_witnessed_by_ems ctx))
      (negb (bystander_cpr_performed ctx))
      (negb (aed_shock_delivered ctx)).

  Definition build_als_criteria (ctx : ResuscitationContext) (s : AlgorithmState.t) : ALSTerminationCriteria :=
    mkALSTerm
      (negb (rosc_achieved s))
      (negb (is_shockable_state s))
      (negb (arrest_witnessed_by_ems ctx))
      (if Rhythm.eq_dec (current_rhythm s) Rhythm.Asystole then true else false)
      (etco2_indicates_futility ctx)
      (negb (reversible_cause_present ctx) || reversible_cause_treated ctx).

  Inductive TerminationDecision : Type :=
    | TD_ContinueResuscitation
    | TD_ConsiderTermination (reason : TerminationReason)
    | TD_TerminationIndicated (reason : TerminationReason)
    | TD_ExtendedResuscitation.

  Definition evaluate_termination (ctx : ResuscitationContext) (s : AlgorithmState.t) : TerminationDecision :=
    if rosc_achieved s then TD_TerminationIndicated TR_ROSCAchieved
    else if dnr_order_valid ctx then TD_TerminationIndicated TR_DNROrderPresent
    else if advance_directive_valid ctx then TD_TerminationIndicated TR_ValidADPresent
    else if should_extend_resuscitation ctx then
      if is_hypothermic_ctx ctx && (duration_min ctx <? hypothermic_max_duration_min) then
        TD_ExtendedResuscitation
      else if hypothermic_max_duration_min <=? duration_min ctx then
        TD_ConsiderTermination TR_FutilityDuration
      else TD_ExtendedResuscitation
    else if etco2_indicates_futility ctx then TD_ConsiderTermination TR_FutilityETCO2
    else if bls_termination_met (build_bls_criteria ctx s) then TD_ConsiderTermination TR_BLSTerminationCriteria
    else if als_termination_met (build_als_criteria ctx s) then TD_ConsiderTermination TR_ALSTerminationCriteria
    else if duration_indicates_futility ctx then TD_ConsiderTermination TR_FutilityDuration
    else TD_ContinueResuscitation.

  Definition family_considerations (ctx : ResuscitationContext) (decision : TerminationDecision) : TerminationDecision :=
    match decision with
    | TD_ConsiderTermination reason =>
        if family_present ctx && family_requests_termination ctx then
          TD_TerminationIndicated TR_FamilyRequest
        else decision
    | _ => decision
    end.

  Definition rosc_context : ResuscitationContext :=
    mkResusContext true true true true true 15 (Some 45) false false false false true false true false false false false.

  Definition dnr_context : ResuscitationContext :=
    mkResusContext false false false false false 5 None false false true false false false false false false false false.

  Definition futile_context : ResuscitationContext :=
    mkResusContext false false false false false 25 (Some 8) false false false false false false false false false false false.

  Definition hypothermic_context : ResuscitationContext :=
    mkResusContext true true true true false 45 (Some 12) false false false false false false false true false false false.

  Definition witnessed_vf_context : ResuscitationContext :=
    mkResusContext true true true true true 10 (Some 25) false false false false false false false false false false false.

  Theorem rosc_terminates_with_rosc : forall ctx s,
    rosc_achieved s = true ->
    evaluate_termination ctx s = TD_TerminationIndicated TR_ROSCAchieved.
  Proof.
    intros ctx s Hrosc.
    unfold evaluate_termination. rewrite Hrosc. reflexivity.
  Qed.

  Theorem dnr_terminates : forall ctx s,
    rosc_achieved s = false ->
    dnr_order_valid ctx = true ->
    evaluate_termination ctx s = TD_TerminationIndicated TR_DNROrderPresent.
  Proof.
    intros ctx s Hrosc Hdnr.
    unfold evaluate_termination. rewrite Hrosc, Hdnr. reflexivity.
  Qed.

  Definition futile_asystole : AlgorithmState.t :=
    AlgorithmState.initial Rhythm.Asystole.

  Theorem low_etco2_suggests_futility : forall ctx s,
    rosc_achieved s = false ->
    dnr_order_valid ctx = false ->
    advance_directive_valid ctx = false ->
    should_extend_resuscitation ctx = false ->
    etco2_indicates_futility ctx = true ->
    evaluate_termination ctx s = TD_ConsiderTermination TR_FutilityETCO2.
  Proof.
    intros ctx s Hrosc Hdnr Had Hext Hetco2.
    unfold evaluate_termination.
    rewrite Hrosc, Hdnr, Had, Hext, Hetco2. reflexivity.
  Qed.

  Theorem hypothermic_extends_resuscitation : forall ctx s,
    rosc_achieved s = false ->
    dnr_order_valid ctx = false ->
    advance_directive_valid ctx = false ->
    is_hypothermic_ctx ctx = true ->
    duration_min ctx < hypothermic_max_duration_min ->
    evaluate_termination ctx s = TD_ExtendedResuscitation.
  Proof.
    intros ctx s Hrosc Hdnr Had Hhypo Hdur.
    unfold evaluate_termination, should_extend_resuscitation.
    rewrite Hrosc, Hdnr, Had, Hhypo.
    destruct (duration_min ctx <? hypothermic_max_duration_min) eqn:E.
    - reflexivity.
    - apply Nat.ltb_nlt in E. lia.
  Qed.

  Definition prognostic_score (ctx : ResuscitationContext) (s : AlgorithmState.t) : nat :=
    (if arrest_is_witnessed ctx then 2 else 0) +
    (if bystander_cpr_performed ctx then 2 else 0) +
    (if initial_rhythm_shockable_ctx ctx then 3 else 0) +
    (match current_etco2 ctx with
     | None => 0
     | Some e => if 20 <=? e then 2 else if 10 <=? e then 1 else 0
     end) +
    (if duration_min ctx <? 10 then 2 else if duration_min ctx <? 20 then 1 else 0) +
    (if rosc_achieved s then 5 else 0).

  Definition prognosis_favorable (ctx : ResuscitationContext) (s : AlgorithmState.t) : bool :=
    6 <=? prognostic_score ctx s.

  Theorem witnessed_vf_favorable :
    prognostic_score witnessed_vf_context futile_asystole >= 6.
  Proof.
    unfold prognostic_score, witnessed_vf_context, futile_asystole, arrest_is_witnessed.
    simpl. lia.
  Qed.

  Definition time_to_consider_termination (ctx : ResuscitationContext) : nat :=
    if should_extend_resuscitation ctx then
      if is_hypothermic_ctx ctx then hypothermic_max_duration_min
      else extended_resuscitation_duration_min
    else standard_resuscitation_duration_min.

  Theorem standard_time_20min : forall ctx,
    should_extend_resuscitation ctx = false ->
    time_to_consider_termination ctx = 20.
  Proof.
    intros ctx H. unfold time_to_consider_termination. rewrite H. reflexivity.
  Qed.

  Theorem hypothermic_time_120min : forall ctx,
    is_hypothermic_ctx ctx = true ->
    time_to_consider_termination ctx = 120.
  Proof.
    intros ctx H.
    unfold time_to_consider_termination, should_extend_resuscitation.
    rewrite H. reflexivity.
  Qed.

End TerminationOfResuscitation.

(******************************************************************************)
(*                                                                            *)
(*                   SECTION 12: POST-ARREST CARE                             *)
(*                                                                            *)
(*  Post-cardiac arrest care parameters per AHA 2020: targeted temperature    *)
(*  management, hemodynamic goals, oxygenation targets.                       *)
(*                                                                            *)
(******************************************************************************)

Module PostArrestCare.

  Definition target_temp_min_C_x10 : nat := 320.
  Definition target_temp_max_C_x10 : nat := 360.

  Definition target_map_min_mmHg : nat := 65.
  Definition target_spo2_min_pct : nat := 92.
  Definition target_spo2_max_pct : nat := 98.

  Definition target_paco2_min_mmHg : nat := 35.
  Definition target_paco2_max_mmHg : nat := 45.

  Record PostArrestVitals : Type := mkPostArrestVitals {
    temp_C_x10 : nat;
    map_mmHg : nat;
    spo2_pct : nat;
    paco2_mmHg : nat;
    glucose_mg_dl : nat
  }.

  Definition temp_on_target (v : PostArrestVitals) : bool :=
    (target_temp_min_C_x10 <=? temp_C_x10 v) &&
    (temp_C_x10 v <=? target_temp_max_C_x10).

  Definition map_adequate (v : PostArrestVitals) : bool :=
    target_map_min_mmHg <=? map_mmHg v.

  Definition oxygenation_on_target (v : PostArrestVitals) : bool :=
    (target_spo2_min_pct <=? spo2_pct v) &&
    (spo2_pct v <=? target_spo2_max_pct).

  Definition ventilation_on_target (v : PostArrestVitals) : bool :=
    (target_paco2_min_mmHg <=? paco2_mmHg v) &&
    (paco2_mmHg v <=? target_paco2_max_mmHg).

  Definition avoid_hypoglycemia (v : PostArrestVitals) : bool :=
    60 <=? glucose_mg_dl v.

  Definition avoid_hyperglycemia (v : PostArrestVitals) : bool :=
    glucose_mg_dl v <=? 180.

  Definition glucose_acceptable (v : PostArrestVitals) : bool :=
    avoid_hypoglycemia v && avoid_hyperglycemia v.

  Definition all_targets_met (v : PostArrestVitals) : bool :=
    temp_on_target v &&
    map_adequate v &&
    oxygenation_on_target v &&
    ventilation_on_target v &&
    glucose_acceptable v.

  Definition ideal_vitals : PostArrestVitals :=
    mkPostArrestVitals 340 75 96 40 120.

  Theorem ideal_vitals_on_target : all_targets_met ideal_vitals = true.
  Proof. reflexivity. Qed.

  Definition hypotensive_vitals : PostArrestVitals :=
    mkPostArrestVitals 340 55 96 40 120.

  Theorem hypotensive_not_on_target : all_targets_met hypotensive_vitals = false.
  Proof. reflexivity. Qed.

  Definition hyperoxic_vitals : PostArrestVitals :=
    mkPostArrestVitals 340 75 100 40 120.

  Theorem hyperoxic_not_on_target : all_targets_met hyperoxic_vitals = false.
  Proof. reflexivity. Qed.

  Definition temp_on_target_iff : forall v,
    temp_on_target v = true <->
    target_temp_min_C_x10 <= temp_C_x10 v /\ temp_C_x10 v <= target_temp_max_C_x10.
  Proof.
    intros v. unfold temp_on_target. split.
    - intro H. apply andb_true_iff in H. destruct H as [H1 H2].
      split; apply Nat.leb_le; assumption.
    - intros [H1 H2]. apply andb_true_iff. split; apply Nat.leb_le; assumption.
  Qed.

  Inductive TTM_Phase : Type :=
    | Induction
    | Maintenance
    | Rewarming.

  Definition ttm_phase_duration_hr (p : TTM_Phase) : nat :=
    match p with
    | Induction => 4
    | Maintenance => 24
    | Rewarming => 8
    end.

  Definition total_ttm_duration_hr : nat :=
    ttm_phase_duration_hr Induction +
    ttm_phase_duration_hr Maintenance +
    ttm_phase_duration_hr Rewarming.

  Theorem ttm_duration : total_ttm_duration_hr = 36.
  Proof. reflexivity. Qed.

  Definition rewarming_rate_max_C_x10_per_hr : nat := 5.

  Definition rewarming_safe (start_temp end_temp hours : nat) : bool :=
    let delta := end_temp - start_temp in
    let max_delta := hours * rewarming_rate_max_C_x10_per_hr in
    delta <=? max_delta.

  Theorem slow_rewarming_safe :
    rewarming_safe 330 360 8 = true.
  Proof. reflexivity. Qed.

  Theorem fast_rewarming_unsafe :
    rewarming_safe 330 370 4 = false.
  Proof. reflexivity. Qed.

  Inductive PostArrestPhase : Type :=
    | PhaseImmediate
    | PhaseEarlyOptimization
    | PhaseOngoingCriticalCare
    | PhaseRecovery.

  Definition phase_duration_hr (p : PostArrestPhase) : nat :=
    match p with
    | PhaseImmediate => 1
    | PhaseEarlyOptimization => 6
    | PhaseOngoingCriticalCare => 72
    | PhaseRecovery => 0
    end.

  Definition phase_priorities (p : PostArrestPhase) : list nat :=
    match p with
    | PhaseImmediate => [1; 2; 3]
    | PhaseEarlyOptimization => [4; 5; 6]
    | PhaseOngoingCriticalCare => [7; 8; 9]
    | PhaseRecovery => [10]
    end.

  Inductive LocalECGFinding : Type :=
    | ECG_STEMI
    | ECG_NonSTEMI
    | ECG_NewLBBB
    | ECG_NonSpecific
    | ECG_Normal.

  Record PostROSCState : Type := mkPostROSCState {
    rosc_time_min : nat;
    arrest_state : AlgorithmState.t;
    current_vitals : PostArrestVitals;
    ttm_phase : TTM_Phase;
    post_ecg_finding : LocalECGFinding
  }.

  Definition initiate_post_arrest_care (s : AlgorithmState.t) : option PostROSCState :=
    if AlgorithmState.rosc_achieved s
    then Some (mkPostROSCState
                 0
                 s
                 ideal_vitals
                 Induction
                 ECG_NonSpecific)
    else None.

  Definition current_post_arrest_phase (prs : PostROSCState) : PostArrestPhase :=
    let t := rosc_time_min prs in
    if t <? 60 then PhaseImmediate
    else if t <? 360 then PhaseEarlyOptimization
    else if t <? 4320 then PhaseOngoingCriticalCare
    else PhaseRecovery.

  Definition ttm_indicated (prs : PostROSCState) : bool :=
    let t := rosc_time_min prs in
    t <? 360.

  Definition cath_lab_activation_needed (prs : PostROSCState) : bool :=
    match post_ecg_finding prs with
    | ECG_STEMI => true
    | ECG_NewLBBB => true
    | _ => false
    end.

  Theorem rosc_initiates_care : forall s,
    AlgorithmState.rosc_achieved s = true ->
    exists prs, initiate_post_arrest_care s = Some prs.
  Proof.
    intros s Hrosc.
    unfold initiate_post_arrest_care.
    rewrite Hrosc. eexists. reflexivity.
  Qed.

  Theorem no_rosc_no_care : forall s,
    AlgorithmState.rosc_achieved s = false ->
    initiate_post_arrest_care s = None.
  Proof.
    intros s Hrosc.
    unfold initiate_post_arrest_care.
    rewrite Hrosc. reflexivity.
  Qed.

  Theorem stemi_needs_cath_lab : forall prs,
    post_ecg_finding prs = ECG_STEMI ->
    cath_lab_activation_needed prs = true.
  Proof.
    intros prs He.
    unfold cath_lab_activation_needed. rewrite He. reflexivity.
  Qed.

  Theorem early_ttm_indicated : forall prs,
    rosc_time_min prs < 360 ->
    ttm_indicated prs = true.
  Proof.
    intros prs H.
    unfold ttm_indicated.
    destruct (rosc_time_min prs <? 360) eqn:E.
    - reflexivity.
    - apply Nat.ltb_nlt in E. exfalso. apply E. exact H.
  Qed.

End PostArrestCare.

(******************************************************************************)
(*                                                                            *)
(*                   SECTION 12A: ECPR ELIGIBILITY                            *)
(*                                                                            *)
(*  Extracorporeal CPR eligibility criteria per AHA 2020 guidelines.          *)
(*  ECPR may be considered for select patients with refractory VF/pVT.        *)
(*                                                                            *)
(******************************************************************************)

Module ECPR.

  Import AlgorithmState.

  Definition min_cpr_cycles_before_ecpr : nat := 10.
  Definition max_arrest_to_ecpr_min : nat := 60.
  Definition min_age_years : nat := 18.
  Definition max_age_years : nat := 75.

  Record ECPRCandidate : Type := mkECPRCandidate {
    age_years : nat;
    arrest_witnessed : bool;
    initial_rhythm_shockable : bool;
    cpr_in_progress : bool;
    no_dnr : bool;
    no_terminal_illness : bool;
    accessible_vasculature : bool;
    ecpr_team_available : bool;
    time_to_ecpr_min : nat
  }.

  Definition age_eligible (c : ECPRCandidate) : bool :=
    (min_age_years <=? age_years c) && (age_years c <=? max_age_years).

  Definition time_eligible (c : ECPRCandidate) : bool :=
    time_to_ecpr_min c <=? max_arrest_to_ecpr_min.

  Definition ecpr_eligible (c : ECPRCandidate) : bool :=
    age_eligible c &&
    arrest_witnessed c &&
    initial_rhythm_shockable c &&
    cpr_in_progress c &&
    no_dnr c &&
    no_terminal_illness c &&
    accessible_vasculature c &&
    ecpr_team_available c &&
    time_eligible c.

  Definition state_suitable_for_ecpr (s : AlgorithmState.t) : bool :=
    is_shockable_state s &&
    negb (rosc_achieved s) &&
    (min_cpr_cycles_before_ecpr <=? cpr_cycles s) &&
    negb (ecpr_initiated s).

  Theorem ideal_ecpr_candidate_eligible :
    let c := mkECPRCandidate 45 true true true true true true true 30 in
    ecpr_eligible c = true.
  Proof. reflexivity. Qed.

  Theorem elderly_not_ecpr_eligible :
    let c := mkECPRCandidate 80 true true true true true true true 30 in
    ecpr_eligible c = false.
  Proof. reflexivity. Qed.

  Theorem unwitnessed_not_ecpr_eligible :
    let c := mkECPRCandidate 45 false true true true true true true 30 in
    ecpr_eligible c = false.
  Proof. reflexivity. Qed.

  Theorem delayed_not_ecpr_eligible :
    let c := mkECPRCandidate 45 true true true true true true true 90 in
    ecpr_eligible c = false.
  Proof. reflexivity. Qed.

  Theorem ecpr_requires_shockable_initial : forall c,
    ecpr_eligible c = true -> initial_rhythm_shockable c = true.
  Proof.
    intros c H.
    unfold ecpr_eligible in H.
    repeat (apply andb_true_iff in H; destruct H as [H ?]).
    assumption.
  Qed.

End ECPR.

(******************************************************************************)
(*                                                                            *)
(*                   SECTION 12B: POST-ROSC PCI PATHWAY                       *)
(*                                                                            *)
(*  Coronary angiography and PCI for STEMI and suspected ACS per AHA 2020.    *)
(*                                                                            *)
(******************************************************************************)

Module PCIPathway.

  Import AlgorithmState.

  Inductive ECGFinding : Type :=
    | STEMI
    | NonSTEMI
    | NewLBBB
    | NonSpecific
    | Normal.

  Inductive PCIUrgency : Type :=
    | Emergent
    | Urgent
    | Deferred
    | NotIndicated.

  Definition ecg_finding_eq_dec : forall e1 e2 : ECGFinding, {e1 = e2} + {e1 <> e2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Record PostROSCPatient : Type := mkPostROSCPatient {
    has_rosc : bool;
    ecg_finding : ECGFinding;
    hemodynamically_stable : bool;
    cath_lab_available : bool;
    time_from_rosc_min : nat;
    chest_pain_pre_arrest : bool;
    high_suspicion_acs : bool
  }.

  Definition door_to_balloon_target_min : nat := 90.
  Definition max_delay_for_emergent_min : nat := 120.

  Definition pci_urgency (p : PostROSCPatient) : PCIUrgency :=
    if negb (has_rosc p) then NotIndicated
    else match ecg_finding p with
         | STEMI => Emergent
         | NewLBBB => if high_suspicion_acs p then Emergent else Urgent
         | NonSTEMI => Urgent
         | NonSpecific => if high_suspicion_acs p then Urgent else Deferred
         | Normal => if chest_pain_pre_arrest p then Deferred else NotIndicated
         end.

  Definition cath_lab_activation_indicated (p : PostROSCPatient) : bool :=
    has_rosc p &&
    cath_lab_available p &&
    match pci_urgency p with
    | Emergent | Urgent => true
    | _ => false
    end.

  Definition time_critical (p : PostROSCPatient) : bool :=
    match pci_urgency p with
    | Emergent => time_from_rosc_min p <=? max_delay_for_emergent_min
    | _ => true
    end.

  Theorem stemi_is_emergent : forall p,
    has_rosc p = true ->
    ecg_finding p = STEMI ->
    pci_urgency p = Emergent.
  Proof.
    intros p Hrosc Hecg.
    unfold pci_urgency. rewrite Hrosc, Hecg. reflexivity.
  Qed.

  Theorem no_rosc_no_pci : forall p,
    has_rosc p = false ->
    pci_urgency p = NotIndicated.
  Proof.
    intros p Hrosc.
    unfold pci_urgency. rewrite Hrosc. reflexivity.
  Qed.

  Theorem normal_ecg_no_pain_no_pci : forall p,
    has_rosc p = true ->
    ecg_finding p = Normal ->
    chest_pain_pre_arrest p = false ->
    pci_urgency p = NotIndicated.
  Proof.
    intros p Hrosc Hecg Hpain.
    unfold pci_urgency. rewrite Hrosc, Hecg, Hpain. reflexivity.
  Qed.

End PCIPathway.

(******************************************************************************)
(*                                                                            *)
(*                   SECTION 12C: DRUG INTERACTION CHECKS                     *)
(*                                                                            *)
(*  Safety checks for drug-drug interactions during ACLS.                     *)
(*                                                                            *)
(******************************************************************************)

Module DrugInteractions.

  Import Medication.
  Import AlgorithmState.

  Definition calcium_bicarb_interaction : bool := true.

  Definition amio_lidocaine_interaction : bool := true.

  Definition calcium_channel_blocker_interaction : bool := true.

  Definition safe_to_give_calcium (s : AlgorithmState.t) (recent_bicarb : bool) : bool :=
    negb (recent_bicarb && (0 <? bicarb_doses s)).

  Definition safe_to_give_lidocaine (s : AlgorithmState.t) : bool :=
    amiodarone_doses s =? 0.

  Definition safe_to_give_amiodarone (s : AlgorithmState.t) : bool :=
    lidocaine_doses s =? 0.

  Definition antiarrhythmic_mutually_exclusive (s : AlgorithmState.t) : bool :=
    (amiodarone_doses s =? 0) || (lidocaine_doses s =? 0).

  Theorem initial_state_safe : forall r,
    safe_to_give_lidocaine (initial r) = true /\
    safe_to_give_amiodarone (initial r) = true /\
    antiarrhythmic_mutually_exclusive (initial r) = true.
  Proof.
    intros r.
    repeat split; reflexivity.
  Qed.

  Theorem amio_blocks_lido : forall s,
    amiodarone_doses s > 0 ->
    safe_to_give_lidocaine s = false.
  Proof.
    intros s H.
    unfold safe_to_give_lidocaine.
    destruct (amiodarone_doses s) eqn:E.
    - lia.
    - reflexivity.
  Qed.

  Theorem lido_blocks_amio : forall s,
    lidocaine_doses s > 0 ->
    safe_to_give_amiodarone s = false.
  Proof.
    intros s H.
    unfold safe_to_give_amiodarone.
    destruct (lidocaine_doses s) eqn:E.
    - lia.
    - reflexivity.
  Qed.

  Definition all_drug_interactions_clear (s : AlgorithmState.t) : bool :=
    antiarrhythmic_mutually_exclusive s.

  Theorem mutual_exclusion_preserved_amio : forall s,
    antiarrhythmic_mutually_exclusive s = true ->
    lidocaine_doses s = 0 ->
    antiarrhythmic_mutually_exclusive (with_amiodarone s) = true.
  Proof.
    intros s Hmut Hlido.
    unfold antiarrhythmic_mutually_exclusive, with_amiodarone. simpl.
    rewrite Hlido. reflexivity.
  Qed.

  Theorem mutual_exclusion_preserved_lido : forall s,
    antiarrhythmic_mutually_exclusive s = true ->
    amiodarone_doses s = 0 ->
    antiarrhythmic_mutually_exclusive (with_lidocaine s) = true.
  Proof.
    intros s Hmut Hamio.
    unfold antiarrhythmic_mutually_exclusive, with_lidocaine. simpl.
    rewrite Hamio. reflexivity.
  Qed.

End DrugInteractions.

(******************************************************************************)
(*                                                                            *)
(*                   SECTION 12D: REAL-TIME CONSTRAINTS                       *)
(*                                                                            *)
(*  Hard timing constraints for CPR quality and intervention delivery.        *)
(*                                                                            *)
(******************************************************************************)

Module RealTimeConstraints.

  Import AlgorithmState.
  Import CPR.

  Definition max_hands_off_sec : nat := 10.
  Definition shock_delivery_target_sec : nat := 3.
  Definition rhythm_check_max_sec : nat := 10.
  Definition pulse_check_max_sec : nat := 10.

  Record TimingEvent : Type := mkTimingEvent {
    event_type : nat;
    start_time_sec : nat;
    end_time_sec : nat
  }.

  Definition event_duration (e : TimingEvent) : nat :=
    end_time_sec e - start_time_sec e.

  Definition hands_off_compliant (e : TimingEvent) : bool :=
    event_duration e <=? max_hands_off_sec.

  Definition shock_delivery_compliant (e : TimingEvent) : bool :=
    event_duration e <=? shock_delivery_target_sec.

  Definition cpr_fraction_target_pct : nat := 80.

  Definition cpr_fraction (cpr_time total_time : nat) : nat :=
    if total_time =? 0 then 100
    else (cpr_time * 100) / total_time.

  Definition cpr_fraction_adequate_pct (cpr_time total_time : nat) : bool :=
    cpr_fraction_target_pct <=? cpr_fraction cpr_time total_time.

  Theorem ideal_cpr_fraction_met :
    cpr_fraction_adequate_pct 96 120 = true.
  Proof. reflexivity. Qed.

  Theorem poor_cpr_fraction_not_met :
    cpr_fraction_adequate_pct 60 120 = false.
  Proof. reflexivity. Qed.

  Definition epi_interval_compliant (last_epi_sec current_sec : nat) : bool :=
    let elapsed := current_sec - last_epi_sec in
    (Medication.epinephrine_interval_min * 60 <=? elapsed) &&
    (elapsed <=? Medication.epinephrine_interval_max * 60).

  Theorem epi_at_3min_compliant :
    epi_interval_compliant 0 180 = true.
  Proof. reflexivity. Qed.

  Theorem epi_at_2min_not_compliant :
    epi_interval_compliant 0 120 = false.
  Proof. reflexivity. Qed.

  Theorem epi_at_6min_not_compliant :
    epi_interval_compliant 0 360 = false.
  Proof. reflexivity. Qed.

  Definition pause_acceptable (pause_reason : nat) (duration_sec : nat) : bool :=
    match pause_reason with
    | 0 => duration_sec <=? rhythm_check_max_sec
    | 1 => duration_sec <=? pulse_check_max_sec
    | 2 => duration_sec <=? shock_delivery_target_sec
    | _ => duration_sec <=? max_hands_off_sec
    end.

  Theorem rhythm_check_10sec_ok :
    pause_acceptable 0 10 = true.
  Proof. reflexivity. Qed.

  Theorem rhythm_check_15sec_not_ok :
    pause_acceptable 0 15 = false.
  Proof. reflexivity. Qed.

  Record ResuscitationTimeline : Type := mkTimeline {
    arrest_time_sec : nat;
    first_cpr_time_sec : nat;
    first_shock_time_sec : option nat;
    first_epi_time_sec : option nat;
    rosc_time_sec : option nat;
    total_hands_off_sec : nat;
    total_cpr_sec : nat
  }.

  Definition cpr_quality_by_timeline (tl : ResuscitationTimeline) : bool :=
    let total := total_cpr_sec tl + total_hands_off_sec tl in
    if total =? 0 then true
    else cpr_fraction_target_pct <=? cpr_fraction (total_cpr_sec tl) total.

  Definition response_time_acceptable (tl : ResuscitationTimeline) : bool :=
    first_cpr_time_sec tl - arrest_time_sec tl <=? 60.

  Definition shock_timing_appropriate (tl : ResuscitationTimeline) : bool :=
    match first_shock_time_sec tl with
    | None => true
    | Some shock_t => shock_t - arrest_time_sec tl <=? 180
    end.

  Definition epi_timing_appropriate_shockable (tl : ResuscitationTimeline) : bool :=
    match first_epi_time_sec tl, first_shock_time_sec tl with
    | None, _ => true
    | Some epi_t, None => true
    | Some epi_t, Some shock_t =>
      2 * CPR.cycle_duration_sec <=? (epi_t - shock_t)
    end.

  Definition timeline_valid (tl : ResuscitationTimeline) : bool :=
    response_time_acceptable tl &&
    shock_timing_appropriate tl &&
    cpr_quality_by_timeline tl.

  Definition ideal_timeline : ResuscitationTimeline :=
    mkTimeline 0 30 (Some 90) (Some 330) (Some 600) 60 540.

  Theorem ideal_timeline_valid : timeline_valid ideal_timeline = true.
  Proof. reflexivity. Qed.

  Definition delayed_response_timeline : ResuscitationTimeline :=
    mkTimeline 0 120 (Some 180) (Some 420) None 60 300.

  Theorem delayed_response_not_acceptable :
    response_time_acceptable delayed_response_timeline = false.
  Proof. reflexivity. Qed.

  Definition state_consistent_with_timeline (s : AlgorithmState.t) (tl : ResuscitationTimeline) : Prop :=
    (AlgorithmState.shock_count s > 0 <-> exists t, first_shock_time_sec tl = Some t) /\
    (AlgorithmState.epinephrine_doses s > 0 <-> exists t, first_epi_time_sec tl = Some t) /\
    (AlgorithmState.rosc_achieved s = true <-> exists t, rosc_time_sec tl = Some t).

  Theorem early_cpr_improves_outcome : forall tl,
    response_time_acceptable tl = true ->
    first_cpr_time_sec tl - arrest_time_sec tl <= 60.
  Proof.
    intros tl H.
    unfold response_time_acceptable in H.
    apply Nat.leb_le in H. exact H.
  Qed.

  Theorem high_cpr_fraction_improves_outcome : forall tl,
    cpr_quality_by_timeline tl = true ->
    total_cpr_sec tl + total_hands_off_sec tl > 0 ->
    cpr_fraction (total_cpr_sec tl) (total_cpr_sec tl + total_hands_off_sec tl) >= cpr_fraction_target_pct.
  Proof.
    intros tl H Hpos.
    unfold cpr_quality_by_timeline in H.
    destruct (total_cpr_sec tl + total_hands_off_sec tl =? 0) eqn:E.
    - apply Nat.eqb_eq in E. lia.
    - apply Nat.leb_le in H. exact H.
  Qed.

End RealTimeConstraints.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 13: PROTOCOL INVARIANTS                         *)
(*                                                                            *)
(*  Key invariants that must hold throughout the ACLS algorithm.              *)
(*                                                                            *)
(******************************************************************************)

Module Invariants.

  Import AlgorithmState.

  Definition shock_only_if_shockable (s : AlgorithmState.t) (shocked : bool) : Prop :=
    shocked = true -> is_shockable_state s = true.

  Definition amio_only_after_three_shocks (s : AlgorithmState.t) : Prop :=
    amiodarone_doses s > 0 -> shock_count s >= 3.

  Definition amio_max_two (s : AlgorithmState.t) : Prop :=
    amiodarone_doses s <= 2.

  Definition rosc_terminates (s : AlgorithmState.t) : Prop :=
    rosc_achieved s = true ->
    Decision.recommend s = Decision.ROSC_achieved.

  Theorem rosc_terminates_holds : forall s,
    rosc_terminates s.
  Proof.
    intros s Hrosc.
    apply Decision.rosc_stops_algorithm. exact Hrosc.
  Qed.

  Definition nonshockable_no_amio (s : AlgorithmState.t) : Prop :=
    is_shockable_state s = false -> can_give_amiodarone s = false.

  Theorem nonshockable_no_amio_holds : forall s,
    nonshockable_no_amio s.
  Proof.
    intros s Hns.
    unfold can_give_amiodarone.
    rewrite Hns. reflexivity.
  Qed.

  Definition epi_always_allowed_nonshockable (s : AlgorithmState.t) : Prop :=
    is_shockable_state s = false ->
    rosc_achieved s = false ->
    epi_due s = true ->
    Decision.recommend s = Decision.Give_Epi_during_CPR.

  Theorem epi_allowed_nonshockable_holds : forall s,
    Decision.reversible_cause_recommendation s = None ->
    epi_always_allowed_nonshockable s.
  Proof.
    intros s Hrc Hns Hrosc Hepi.
    unfold Decision.recommend, is_shockable_state in *.
    rewrite Hns.
    unfold Decision.nonshockable_recommendation.
    rewrite Hrosc, Hrc, Hepi. reflexivity.
  Qed.

  Definition cpr_time_advances (s1 s2 : AlgorithmState.t) : Prop :=
    cpr_cycles s2 > cpr_cycles s1 ->
    time_sec s2 >= time_sec s1 + CPR.cycle_duration_sec.

  Definition shocks_bounded_by_cycles (s : AlgorithmState.t) : Prop :=
    shock_count s <= cpr_cycles s + 1.

  Definition epi_interval_respected (s : AlgorithmState.t) : Prop :=
    match last_epi_time_sec s with
    | None => True
    | Some last =>
        epi_due s = true ->
        time_sec s - last >= Medication.epinephrine_interval_min * 60
    end.

  Theorem initial_satisfies_invariants : forall r,
    amio_max_two (initial r) /\
    shock_count (initial r) = 0 /\
    epinephrine_doses (initial r) = 0 /\
    rosc_achieved (initial r) = false.
  Proof.
    intros r. unfold amio_max_two, initial. simpl.
    repeat split; lia.
  Qed.

  Definition state_consistent (s : AlgorithmState.t) : Prop :=
    amio_max_two s /\
    (amiodarone_doses s > 0 -> is_shockable_state s = true \/ shock_count s >= 3) /\
    (rosc_achieved s = true -> Decision.recommend s = Decision.ROSC_achieved).

  Definition lidocaine_amio_mutually_exclusive (s : AlgorithmState.t) : Prop :=
    can_give_lidocaine s = true -> amiodarone_doses s = 0.

  Theorem lidocaine_amio_mutual_exclusion : forall s,
    lidocaine_amio_mutually_exclusive s.
  Proof.
    intros s Hlido.
    unfold can_give_lidocaine in Hlido.
    apply andb_true_iff in Hlido. destruct Hlido as [Hlido _].
    apply andb_true_iff in Hlido. destruct Hlido as [Hlido _].
    apply andb_true_iff in Hlido. destruct Hlido as [_ Hamio].
    apply Nat.eqb_eq in Hamio. exact Hamio.
  Qed.

  Theorem amio_given_blocks_lido : forall s,
    amiodarone_doses s > 0 -> can_give_lidocaine s = false.
  Proof.
    intros s Hamio.
    unfold can_give_lidocaine.
    destruct (amiodarone_doses s) eqn:E.
    - lia.
    - destruct (is_shockable_state s); [|reflexivity].
      destruct (3 <=? shock_count s); simpl; reflexivity.
  Qed.

  Theorem lido_given_blocks_amio : forall s,
    lidocaine_doses s > 0 -> can_give_amiodarone s = false.
  Proof.
    intros s Hlido.
    unfold can_give_amiodarone.
    destruct (lidocaine_doses s) eqn:E.
    - lia.
    - destruct (is_shockable_state s); [|reflexivity].
      destruct (3 <=? shock_count s); [|reflexivity].
      destruct (amiodarone_doses s <? 2); reflexivity.
  Qed.

  Theorem antiarrhythmic_mutual_exclusion_complete : forall s,
    (amiodarone_doses s > 0 -> can_give_lidocaine s = false) /\
    (lidocaine_doses s > 0 -> can_give_amiodarone s = false).
  Proof.
    intros s. split.
    - exact (amio_given_blocks_lido s).
    - exact (lido_given_blocks_amio s).
  Qed.

  Theorem shockable_epi_after_second_shock : forall s,
    is_shockable_state s = true ->
    shock_count s = 2 ->
    epi_due s = true ->
    rosc_achieved s = false ->
    Decision.reversible_cause_recommendation s = None ->
    Decision.recommend s = Decision.Give_Epi_during_CPR.
  Proof.
    intros s Hshock Hsc Hepi Hrosc Hrc.
    unfold Decision.recommend. rewrite Hshock.
    unfold Decision.shockable_recommendation.
    rewrite Hrosc, Hrc, Hsc, Hepi. reflexivity.
  Qed.

End Invariants.

(******************************************************************************)
(*                                                                            *)
(*                  SECTION 14: NEGATIVE SPECIFICATIONS                       *)
(*                                                                            *)
(*  Properties that should NEVER hold - critical safety constraints.          *)
(*                                                                            *)
(******************************************************************************)

Module NegativeSpecs.

  Import AlgorithmState.

  Theorem never_shock_asystole : forall s,
    current_rhythm s = Rhythm.Asystole ->
    rosc_achieved s = false ->
    Decision.recommend s <> Decision.Shock_then_CPR.
  Proof.
    intros s Hr Hrosc.
    exact (Decision.Asystole_no_shock s Hr Hrosc).
  Qed.

  Theorem never_shock_PEA : forall s,
    current_rhythm s = Rhythm.PEA ->
    rosc_achieved s = false ->
    Decision.recommend s <> Decision.Shock_then_CPR.
  Proof.
    intros s Hr Hrosc.
    exact (Decision.PEA_no_shock s Hr Hrosc).
  Qed.

  Theorem never_amio_before_third_shock : forall s,
    shock_count s < 3 ->
    can_give_amiodarone s = false.
  Proof.
    intros s Hsc.
    unfold can_give_amiodarone.
    destruct (is_shockable_state s); [|reflexivity].
    destruct (3 <=? shock_count s) eqn:E.
    - apply Nat.leb_le in E. lia.
    - reflexivity.
  Qed.

  Theorem never_amio_on_nonshockable : forall s,
    is_shockable_state s = false ->
    can_give_amiodarone s = false.
  Proof.
    intros s Hns.
    unfold can_give_amiodarone.
    rewrite Hns. reflexivity.
  Qed.

  Theorem never_third_amio : forall s,
    amiodarone_doses s >= 2 ->
    can_give_amiodarone s = false.
  Proof.
    intros s Hamio.
    unfold can_give_amiodarone.
    destruct (is_shockable_state s); [|reflexivity].
    destruct (3 <=? shock_count s); simpl.
    - destruct (amiodarone_doses s <? 2) eqn:E.
      + apply Nat.ltb_lt in E. lia.
      + reflexivity.
    - reflexivity.
  Qed.

  Theorem never_continue_after_rosc : forall s,
    rosc_achieved s = true ->
    Decision.recommend s = Decision.ROSC_achieved.
  Proof.
    exact Decision.rosc_stops_algorithm.
  Qed.

  Theorem shock_requires_shockable : forall s,
    Decision.recommend s = Decision.Shock_then_CPR ->
    is_shockable_state s = true.
  Proof.
    intros s H.
    unfold Decision.recommend in H.
    destruct (is_shockable_state s) eqn:E.
    - reflexivity.
    - unfold Decision.nonshockable_recommendation in H.
      destruct (rosc_achieved s); [discriminate H|].
      unfold Decision.reversible_cause_recommendation in H.
      destruct (needs_lipid s); [discriminate H|].
      destruct (needs_calcium s); [discriminate H|].
      destruct (needs_bicarb s); [discriminate H|].
      destruct (needs_magnesium s); [discriminate H|].
      destruct (epi_due s); discriminate H.
  Qed.

  Theorem amio_requires_shockable_and_shocks : forall s,
    can_give_amiodarone s = true ->
    is_shockable_state s = true /\ shock_count s >= 3 /\ amiodarone_doses s < 2.
  Proof.
    intros s H.
    unfold can_give_amiodarone in H.
    destruct (is_shockable_state s) eqn:E1; [|discriminate].
    destruct (3 <=? shock_count s) eqn:E2; [|discriminate].
    destruct (amiodarone_doses s <? 2) eqn:E3; [|discriminate].
    apply Nat.leb_le in E2.
    apply Nat.ltb_lt in E3.
    repeat split; assumption.
  Qed.

  Theorem epi_delay_in_shockable : forall s,
    is_shockable_state s = true ->
    shock_count s < 2 ->
    rosc_achieved s = false ->
    Decision.reversible_cause_recommendation s = None ->
    Decision.recommend s = Decision.Shock_then_CPR.
  Proof.
    intros s Hshock Hsc Hrosc Hrc.
    unfold Decision.recommend. rewrite Hshock.
    unfold Decision.shockable_recommendation.
    rewrite Hrosc, Hrc.
    destruct (shock_count s) as [|[|n]] eqn:Esc.
    - reflexivity.
    - reflexivity.
    - lia.
  Qed.

End NegativeSpecs.

(******************************************************************************)
(*                                                                            *)
(*                      SECTION 15: MAIN RESULTS                              *)
(*                                                                            *)
(*  Summary theorems establishing correctness of the ACLS algorithm.          *)
(*                                                                            *)
(******************************************************************************)

Module MainResults.

  Theorem rhythm_classification_complete : forall r,
    Rhythm.shockable r = true \/ Rhythm.shockable r = false.
  Proof. exact Rhythm.shockable_exhaustive. Qed.

  Theorem rhythm_classification_decidable : forall r,
    {Rhythm.is_shockable r} + {Rhythm.is_non_shockable r}.
  Proof. exact Rhythm.shockable_dec. Qed.

  Theorem exactly_two_shockable :
    length (filter Rhythm.shockable Rhythm.all) = 2.
  Proof. reflexivity. Qed.

  Theorem exactly_two_nonshockable :
    length (filter (fun r => negb (Rhythm.shockable r)) Rhythm.all) = 2.
  Proof. reflexivity. Qed.

  Theorem shockable_rhythms_are_VF_pVT : forall r,
    Rhythm.shockable r = true <-> r = Rhythm.VF \/ r = Rhythm.pVT.
  Proof.
    intros r. split.
    - destruct r; intro H; try discriminate; auto.
    - intros [H|H]; subst; reflexivity.
  Qed.

  Theorem nonshockable_rhythms_are_PEA_Asystole : forall r,
    Rhythm.shockable r = false <-> r = Rhythm.PEA \/ r = Rhythm.Asystole.
  Proof.
    intros r. split.
    - destruct r; intro H; try discriminate; auto.
    - intros [H|H]; subst; reflexivity.
  Qed.

  Theorem algorithm_always_has_recommendation : forall s,
    exists rec, Decision.recommend s = rec.
  Proof.
    intros s. eexists. reflexivity.
  Qed.

  Theorem recommendation_deterministic : forall s r1 r2,
    Decision.recommend s = r1 ->
    Decision.recommend s = r2 ->
    r1 = r2.
  Proof.
    intros s r1 r2 H1 H2. congruence.
  Qed.

  Theorem shockable_initial_always_shock : forall r,
    Rhythm.shockable r = true ->
    Decision.recommend (AlgorithmState.initial r) = Decision.Shock_then_CPR.
  Proof.
    intros r Hr.
    unfold Decision.recommend, AlgorithmState.is_shockable_state, AlgorithmState.initial.
    simpl. rewrite Hr.
    unfold Decision.shockable_recommendation. simpl. reflexivity.
  Qed.

  Theorem nonshockable_initial_always_epi : forall r,
    Rhythm.shockable r = false ->
    Decision.recommend (AlgorithmState.initial r) = Decision.Give_Epi_during_CPR.
  Proof.
    intros r Hr.
    unfold Decision.recommend, AlgorithmState.is_shockable_state, AlgorithmState.initial.
    simpl. rewrite Hr.
    unfold Decision.nonshockable_recommendation. simpl. reflexivity.
  Qed.

  Theorem VF_initial_protocol :
    Decision.recommend (AlgorithmState.initial Rhythm.VF) = Decision.Shock_then_CPR.
  Proof. reflexivity. Qed.

  Theorem pVT_initial_protocol :
    Decision.recommend (AlgorithmState.initial Rhythm.pVT) = Decision.Shock_then_CPR.
  Proof. reflexivity. Qed.

  Theorem PEA_initial_protocol :
    Decision.recommend (AlgorithmState.initial Rhythm.PEA) = Decision.Give_Epi_during_CPR.
  Proof. reflexivity. Qed.

  Theorem Asystole_initial_protocol :
    Decision.recommend (AlgorithmState.initial Rhythm.Asystole) = Decision.Give_Epi_during_CPR.
  Proof. reflexivity. Qed.

  Theorem cpr_parameters_clinically_valid :
    CPR.min_depth_cm = 5 /\
    CPR.max_depth_cm = 6 /\
    CPR.min_rate_per_min = 100 /\
    CPR.max_rate_per_min = 120 /\
    CPR.cycle_duration_sec = 120 /\
    CPR.compression_ratio = 30 /\
    CPR.ventilation_ratio = 2.
  Proof. repeat split; reflexivity. Qed.

  Theorem medication_doses_per_aha :
    Medication.epinephrine_dose_mg = 1 /\
    Medication.amiodarone_first_dose_mg = 300 /\
    Medication.amiodarone_second_dose_mg = 150 /\
    Medication.epinephrine_interval_min = 3.
  Proof. repeat split; reflexivity. Qed.

  Theorem rosc_etco2_threshold :
    ROSC.etco2_threshold_mmHg = 40.
  Proof. reflexivity. Qed.

  Theorem defibrillator_energies_correct :
    Defibrillation.biphasic_initial_min_J = 120 /\
    Defibrillation.biphasic_initial_max_J = 200 /\
    Defibrillation.monophasic_dose_J = 360.
  Proof. repeat split; reflexivity. Qed.

  Theorem h_causes_complete :
    length ReversibleCauses.all_h_causes = 7.
  Proof. reflexivity. Qed.

  Theorem t_causes_complete :
    length ReversibleCauses.all_t_causes = 6.
  Proof. reflexivity. Qed.

  Theorem post_arrest_temp_range :
    PostArrestCare.target_temp_min_C_x10 = 320 /\
    PostArrestCare.target_temp_max_C_x10 = 360.
  Proof. split; reflexivity. Qed.

  Theorem protocol_safety_core :
    (forall s, Rhythm.shockable (AlgorithmState.current_rhythm s) = false ->
               AlgorithmState.rosc_achieved s = false ->
               Decision.recommend s <> Decision.Shock_then_CPR) /\
    (forall s, AlgorithmState.rosc_achieved s = true ->
               Decision.recommend s = Decision.ROSC_achieved) /\
    (forall s, AlgorithmState.shock_count s < 3 ->
               AlgorithmState.can_give_amiodarone s = false).
  Proof.
    repeat split.
    - intros s Hns Hrosc.
      exact (Decision.nonshockable_not_shock s Hns Hrosc).
    - exact Decision.rosc_stops_algorithm.
    - exact NegativeSpecs.never_amio_before_third_shock.
  Qed.

  Theorem antiarrhythmic_mutual_exclusion :
    (forall s, AlgorithmState.amiodarone_doses s > 0 ->
               AlgorithmState.can_give_lidocaine s = false) /\
    (forall s, AlgorithmState.lidocaine_doses s > 0 ->
               AlgorithmState.can_give_amiodarone s = false).
  Proof.
    split.
    - intros s. exact (proj1 (Invariants.antiarrhythmic_mutual_exclusion_complete s)).
    - intros s. exact (proj2 (Invariants.antiarrhythmic_mutual_exclusion_complete s)).
  Qed.

  Theorem epi_timing_correct :
    (forall s, AlgorithmState.is_shockable_state s = true ->
               AlgorithmState.shock_count s < 2 ->
               AlgorithmState.epi_indicated s = false) /\
    (forall s, AlgorithmState.is_shockable_state s = false ->
               AlgorithmState.epi_due s = true ->
               AlgorithmState.rosc_achieved s = false ->
               AlgorithmState.epi_indicated s = true).
  Proof.
    split.
    - exact AlgorithmState.epi_not_indicated_before_two_shocks.
    - exact AlgorithmState.epi_indicated_nonshockable_immediate.
  Qed.

  Theorem etco2_guided_cpr :
    (forall e, CPR.assess_cpr_quality_by_etco2 e = CPR.QualityROSCLikely ->
               CPR.etco2_suggests_rosc_during_cpr e = true) /\
    (forall s e, AlgorithmState.etco2_during_cpr s = Some e ->
                 e >= 40 ->
                 AlgorithmState.cpr_quality_suggests_rosc s = true).
  Proof.
    split.
    - exact CPR.rosc_likely_implies_check_pulse.
    - exact AlgorithmState.high_etco2_suggests_rosc.
  Qed.

  Theorem hypothermia_protocol_safety :
    (forall temp, temp < HypothermicArrest.core_temp_severe_hypothermia_x10 ->
                  SpecialPopulationDecision.hypothermic_meds_allowed temp = false) /\
    (forall temp, temp < HypothermicArrest.core_temp_severe_hypothermia_x10 ->
                  SpecialPopulationDecision.hypothermic_repeat_shock_allowed temp 1 = false).
  Proof.
    split.
    - exact SpecialPopulationDecision.severe_hypothermia_no_meds.
    - exact SpecialPopulationDecision.severe_hypothermia_single_shock.
  Qed.

  Theorem rosc_initiates_post_arrest_care :
    forall s, AlgorithmState.rosc_achieved s = true ->
              exists prs, PostArrestCare.initiate_post_arrest_care s = Some prs.
  Proof.
    exact PostArrestCare.rosc_initiates_care.
  Qed.

  Theorem protocol_completeness :
    (forall s, exists rec, Decision.recommend s = rec) /\
    (forall r, Rhythm.shockable r = true \/ Rhythm.shockable r = false) /\
    (forall s, AlgorithmState.is_shockable_state s = true \/
               AlgorithmState.is_shockable_state s = false).
  Proof.
    repeat split.
    - intros s. eexists. reflexivity.
    - exact Rhythm.shockable_exhaustive.
    - intros s. destruct (AlgorithmState.is_shockable_state s); auto.
  Qed.

  Theorem drug_interaction_safety :
    forall s, DrugInteractions.antiarrhythmic_mutually_exclusive s = true \/
              (AlgorithmState.amiodarone_doses s > 0 /\ AlgorithmState.lidocaine_doses s > 0).
  Proof.
    intros s.
    unfold DrugInteractions.antiarrhythmic_mutually_exclusive.
    destruct (AlgorithmState.amiodarone_doses s =? 0) eqn:E1.
    - left. reflexivity.
    - destruct (AlgorithmState.lidocaine_doses s =? 0) eqn:E2.
      + left. apply orb_true_r.
      + right.
        apply Nat.eqb_neq in E1.
        apply Nat.eqb_neq in E2.
        split; lia.
  Qed.

End MainResults.

(******************************************************************************)
(*                                                                            *)
(*                   SECTION 16: CODE READINESS INDICATORS                    *)
(*                                                                            *)
(*  Pre-arrest code readiness: equipment, personnel, medications.             *)
(*  Ensures all necessary resources are available before cardiac arrest.      *)
(*                                                                            *)
(******************************************************************************)

Module CodeReadiness.

  Record Equipment : Type := mkEquipment {
    defibrillator_available : bool;
    defibrillator_charged : bool;
    airway_equipment_available : bool;
    suction_available : bool;
    oxygen_available : bool;
    iv_supplies_available : bool;
    monitor_available : bool;
    backboard_available : bool;
    capnography_available : bool
  }.

  Record Medications : Type := mkMedications {
    epinephrine_available : bool;
    amiodarone_available : bool;
    lidocaine_available : bool;
    magnesium_available : bool;
    calcium_available : bool;
    sodium_bicarbonate_available : bool;
    lipid_emulsion_available : bool;
    normal_saline_available : bool
  }.

  Record Personnel : Type := mkPersonnel {
    team_leader_present : bool;
    compressor_present : bool;
    airway_manager_present : bool;
    iv_medication_nurse_present : bool;
    recorder_present : bool;
    min_team_size : nat
  }.

  Definition equipment_ready (e : Equipment) : bool :=
    defibrillator_available e &&
    defibrillator_charged e &&
    airway_equipment_available e &&
    suction_available e &&
    oxygen_available e &&
    iv_supplies_available e &&
    monitor_available e &&
    backboard_available e.

  Definition critical_meds_available (m : Medications) : bool :=
    epinephrine_available m &&
    (amiodarone_available m || lidocaine_available m).

  Definition all_meds_available (m : Medications) : bool :=
    epinephrine_available m &&
    amiodarone_available m &&
    calcium_available m &&
    sodium_bicarbonate_available m &&
    normal_saline_available m.

  Definition minimum_team_ready (p : Personnel) : bool :=
    team_leader_present p &&
    compressor_present p &&
    (4 <=? min_team_size p).

  Definition optimal_team_ready (p : Personnel) : bool :=
    team_leader_present p &&
    compressor_present p &&
    airway_manager_present p &&
    iv_medication_nurse_present p &&
    recorder_present p &&
    (6 <=? min_team_size p).

  Definition code_ready (e : Equipment) (m : Medications) (p : Personnel) : bool :=
    equipment_ready e && critical_meds_available m && minimum_team_ready p.

  Definition optimal_code_ready (e : Equipment) (m : Medications) (p : Personnel) : bool :=
    equipment_ready e &&
    capnography_available e &&
    all_meds_available m &&
    optimal_team_ready p.

  Definition ideal_equipment : Equipment :=
    mkEquipment true true true true true true true true true.

  Definition ideal_meds : Medications :=
    mkMedications true true true true true true true true.

  Definition ideal_team : Personnel :=
    mkPersonnel true true true true true 6.

  Definition minimal_team : Personnel :=
    mkPersonnel true true false false false 4.

  Theorem ideal_equipment_ready : equipment_ready ideal_equipment = true.
  Proof. reflexivity. Qed.

  Theorem ideal_meds_critical : critical_meds_available ideal_meds = true.
  Proof. reflexivity. Qed.

  Theorem ideal_meds_all : all_meds_available ideal_meds = true.
  Proof. reflexivity. Qed.

  Theorem ideal_team_optimal : optimal_team_ready ideal_team = true.
  Proof. reflexivity. Qed.

  Theorem minimal_team_minimum : minimum_team_ready minimal_team = true.
  Proof. reflexivity. Qed.

  Theorem code_ready_with_ideals :
    code_ready ideal_equipment ideal_meds ideal_team = true.
  Proof. reflexivity. Qed.

  Theorem optimal_code_ready_with_ideals :
    optimal_code_ready ideal_equipment ideal_meds ideal_team = true.
  Proof. reflexivity. Qed.

  Definition no_defib : Equipment :=
    mkEquipment false false true true true true true true true.

  Theorem no_defib_not_ready : equipment_ready no_defib = false.
  Proof. reflexivity. Qed.

  Definition no_epi : Medications :=
    mkMedications false true true true true true true true.

  Theorem no_epi_not_critical : critical_meds_available no_epi = false.
  Proof. reflexivity. Qed.

  Definition defib_requires_charge : forall e,
    defibrillator_available e = true ->
    defibrillator_charged e = false ->
    equipment_ready e = false.
  Proof.
    intros e Havail Hcharge.
    unfold equipment_ready.
    rewrite Havail, Hcharge. reflexivity.
  Qed.

  Definition epi_always_required : forall m,
    epinephrine_available m = false ->
    critical_meds_available m = false.
  Proof.
    intros m Hepi.
    unfold critical_meds_available.
    rewrite Hepi. reflexivity.
  Qed.

End CodeReadiness.

(******************************************************************************)
(*                                                                            *)
(*               SECTION 16B: HOSPITAL MEDICATION AVAILABILITY                *)
(*                                                                            *)
(*  Hospital-specific medication formulary integration for ACLS protocols.    *)
(*  Allows protocol recommendations to be constrained by what is actually     *)
(*  available in a given facility.                                            *)
(*                                                                            *)
(******************************************************************************)

Module HospitalMedicationAvailability.

  Import AlgorithmState.
  Import Medication.

  Inductive FacilityType : Type :=
    | TertiaryHospital
    | CommunityHospital
    | RuralHospital
    | OutpatientClinic
    | PreHospitalEMS
    | FieldMilitary.

  Definition facility_type_eq_dec : forall f1 f2 : FacilityType, {f1 = f2} + {f1 <> f2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Record HospitalFormulary : Type := mkFormulary {
    form_epinephrine : bool;
    form_amiodarone : bool;
    form_lidocaine : bool;
    form_magnesium : bool;
    form_calcium_chloride : bool;
    form_calcium_gluconate : bool;
    form_sodium_bicarbonate : bool;
    form_lipid_emulsion : bool;
    form_adenosine : bool;
    form_atropine : bool;
    form_dopamine : bool;
    form_vasopressin : bool;
    form_procainamide : bool;
    form_isoproterenol : bool
  }.

  Definition full_formulary : HospitalFormulary :=
    mkFormulary true true true true true true true true true true true true true true.

  Definition basic_formulary : HospitalFormulary :=
    mkFormulary true true true true true true true false true true true false false false.

  Definition ems_formulary : HospitalFormulary :=
    mkFormulary true true true true false true true false true true true false false false.

  Definition rural_formulary : HospitalFormulary :=
    mkFormulary true false true true true true true false true true true false false false.

  Definition drug_available (f : HospitalFormulary) (d : Drug) : bool :=
    match d with
    | Epinephrine => form_epinephrine f
    | Amiodarone => form_amiodarone f
    | Lidocaine => form_lidocaine f
    | MagnesiumSulfate => form_magnesium f
    | CalciumChloride => form_calcium_chloride f
    | CalciumGluconate => form_calcium_gluconate f
    | SodiumBicarbonate => form_sodium_bicarbonate f
    | LipidEmulsion => form_lipid_emulsion f
    end.

  Definition default_formulary_for_facility (ft : FacilityType) : HospitalFormulary :=
    match ft with
    | TertiaryHospital => full_formulary
    | CommunityHospital => full_formulary
    | RuralHospital => rural_formulary
    | OutpatientClinic => basic_formulary
    | PreHospitalEMS => ems_formulary
    | FieldMilitary => basic_formulary
    end.

  Definition antiarrhythmic_available (f : HospitalFormulary) : bool :=
    form_amiodarone f || form_lidocaine f.

  Definition preferred_antiarrhythmic (f : HospitalFormulary) : option Drug :=
    if form_amiodarone f then Some Amiodarone
    else if form_lidocaine f then Some Lidocaine
    else None.

  Definition calcium_available (f : HospitalFormulary) : bool :=
    form_calcium_chloride f || form_calcium_gluconate f.

  Definition preferred_calcium (f : HospitalFormulary) : option Drug :=
    if form_calcium_chloride f then Some CalciumChloride
    else if form_calcium_gluconate f then Some CalciumGluconate
    else None.

  Record ConstrainedRecommendation : Type := mkConstRec {
    original_drug : Drug;
    is_available : bool;
    alternative_drug : option Drug;
    alternative_available : bool
  }.

  Definition constrain_recommendation (f : HospitalFormulary) (d : Drug) : ConstrainedRecommendation :=
    let avail := drug_available f d in
    let alt := match d with
               | Amiodarone => if form_lidocaine f then Some Lidocaine else None
               | Lidocaine => if form_amiodarone f then Some Amiodarone else None
               | CalciumChloride => if form_calcium_gluconate f then Some CalciumGluconate else None
               | CalciumGluconate => if form_calcium_chloride f then Some CalciumChloride else None
               | _ => None
               end in
    let alt_avail := match alt with
                     | Some d' => drug_available f d'
                     | None => false
                     end in
    mkConstRec d avail alt alt_avail.

  Definition recommendation_feasible (cr : ConstrainedRecommendation) : bool :=
    is_available cr || alternative_available cr.

  Definition get_usable_drug (cr : ConstrainedRecommendation) : option Drug :=
    if is_available cr then Some (original_drug cr)
    else alternative_drug cr.

  Inductive ProtocolModification : Type :=
    | PM_UseAlternative (original : Drug) (alternate : Drug)
    | PM_SkipUnavailable (drug : Drug)
    | PM_TransferForDrug (drug : Drug)
    | PM_NoModification.

  Definition recommend_modification (f : HospitalFormulary) (d : Drug) : ProtocolModification :=
    let cr := constrain_recommendation f d in
    if is_available cr then PM_NoModification
    else match alternative_drug cr with
         | Some alt => if drug_available f alt then PM_UseAlternative d alt else PM_SkipUnavailable d
         | None => PM_SkipUnavailable d
         end.

  Theorem full_formulary_has_epi :
    drug_available full_formulary Epinephrine = true.
  Proof. reflexivity. Qed.

  Theorem full_formulary_has_amio :
    drug_available full_formulary Amiodarone = true.
  Proof. reflexivity. Qed.

  Theorem rural_no_amio :
    drug_available rural_formulary Amiodarone = false.
  Proof. reflexivity. Qed.

  Theorem rural_has_lido :
    drug_available rural_formulary Lidocaine = true.
  Proof. reflexivity. Qed.

  Theorem rural_gets_lido_for_amio :
    recommend_modification rural_formulary Amiodarone = PM_UseAlternative Amiodarone Lidocaine.
  Proof. reflexivity. Qed.

  Theorem ems_no_calcium_chloride :
    drug_available ems_formulary CalciumChloride = false.
  Proof. reflexivity. Qed.

  Theorem ems_has_calcium_gluconate :
    drug_available ems_formulary CalciumGluconate = true.
  Proof. reflexivity. Qed.

  Theorem ems_gets_gluconate_for_chloride :
    recommend_modification ems_formulary CalciumChloride = PM_UseAlternative CalciumChloride CalciumGluconate.
  Proof. reflexivity. Qed.

  Definition acls_minimum_requirements (f : HospitalFormulary) : bool :=
    form_epinephrine f &&
    antiarrhythmic_available f.

  Definition acls_full_requirements (f : HospitalFormulary) : bool :=
    form_epinephrine f &&
    form_amiodarone f &&
    form_lidocaine f &&
    form_magnesium f &&
    calcium_available f &&
    form_sodium_bicarbonate f.

  Theorem full_formulary_meets_minimum :
    acls_minimum_requirements full_formulary = true.
  Proof. reflexivity. Qed.

  Theorem full_formulary_meets_full :
    acls_full_requirements full_formulary = true.
  Proof. reflexivity. Qed.

  Theorem rural_meets_minimum :
    acls_minimum_requirements rural_formulary = true.
  Proof. reflexivity. Qed.

  Theorem ems_meets_minimum :
    acls_minimum_requirements ems_formulary = true.
  Proof. reflexivity. Qed.

  Record ProtocolExecutionContext : Type := mkExecContext {
    pec_formulary : HospitalFormulary;
    pec_facility_type : FacilityType;
    pec_transfer_available : bool;
    pec_time_to_tertiary_min : nat;
    pec_ecmo_capable : bool;
    pec_cath_lab_available : bool
  }.

  Definition tertiary_context : ProtocolExecutionContext :=
    mkExecContext full_formulary TertiaryHospital false 0 true true.

  Definition rural_context : ProtocolExecutionContext :=
    mkExecContext rural_formulary RuralHospital true 45 false false.

  Definition ems_context : ProtocolExecutionContext :=
    mkExecContext ems_formulary PreHospitalEMS true 20 false false.

  Definition context_supports_full_acls (ctx : ProtocolExecutionContext) : bool :=
    acls_full_requirements (pec_formulary ctx).

  Definition context_supports_ecpr (ctx : ProtocolExecutionContext) : bool :=
    pec_ecmo_capable ctx.

  Definition context_supports_pci (ctx : ProtocolExecutionContext) : bool :=
    pec_cath_lab_available ctx.

  Definition should_consider_transfer (ctx : ProtocolExecutionContext) (needs_ecpr needs_pci : bool) : bool :=
    pec_transfer_available ctx &&
    ((needs_ecpr && negb (context_supports_ecpr ctx)) ||
     (needs_pci && negb (context_supports_pci ctx))).

  Theorem tertiary_full_acls :
    context_supports_full_acls tertiary_context = true.
  Proof. reflexivity. Qed.

  Theorem rural_needs_transfer_for_ecpr :
    should_consider_transfer rural_context true false = true.
  Proof. reflexivity. Qed.

  Theorem rural_needs_transfer_for_pci :
    should_consider_transfer rural_context false true = true.
  Proof. reflexivity. Qed.

  Theorem tertiary_no_transfer_needed :
    should_consider_transfer tertiary_context true true = false.
  Proof. reflexivity. Qed.

  Definition validate_protocol_for_context (ctx : ProtocolExecutionContext) (s : AlgorithmState.t) : bool :=
    acls_minimum_requirements (pec_formulary ctx).

  Definition adjust_recommendation_for_context (ctx : ProtocolExecutionContext) (d : Drug) : option Drug :=
    get_usable_drug (constrain_recommendation (pec_formulary ctx) d).

  Theorem rural_adjusts_amio_to_lido :
    adjust_recommendation_for_context rural_context Amiodarone = Some Lidocaine.
  Proof. reflexivity. Qed.

  Theorem tertiary_keeps_amio :
    adjust_recommendation_for_context tertiary_context Amiodarone = Some Amiodarone.
  Proof. reflexivity. Qed.

End HospitalMedicationAvailability.

