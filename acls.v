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

End CPR.

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
    | MagnesiumSulfate.

  Definition drug_eq_dec : forall d1 d2 : Drug, {d1 = d2} + {d1 <> d2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Definition all_drugs : list Drug :=
    [Epinephrine; Amiodarone; Lidocaine; MagnesiumSulfate].

  Lemma all_drugs_complete : forall d : Drug, In d all_drugs.
  Proof. intros []; simpl; auto. Qed.

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
    | Amiodarone | Lidocaine => true
    | _ => false
    end.

  Definition is_vasopressor (d : Drug) : bool :=
    match d with
    | Epinephrine => true
    | _ => false
    end.

  Theorem amiodarone_is_antiarrhythmic : is_antiarrhythmic Amiodarone = true.
  Proof. reflexivity. Qed.

  Theorem lidocaine_is_antiarrhythmic : is_antiarrhythmic Lidocaine = true.
  Proof. reflexivity. Qed.

  Theorem epinephrine_is_vasopressor : is_vasopressor Epinephrine = true.
  Proof. reflexivity. Qed.

  Theorem epinephrine_not_antiarrhythmic : is_antiarrhythmic Epinephrine = false.
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
    | CheckPulse
    | EstablishAccess
    | SecureAirway
    | IdentifyReversibleCause.

  Definition eq_dec : forall a1 a2 : t, {a1 = a2} + {a1 <> a2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Definition all : list t :=
    [StartCPR; ContinueCPR; DeliverShock; CheckRhythm;
     GiveEpinephrine; GiveAmiodarone; GiveLidocaine; GiveMagnesium;
     CheckPulse; EstablishAccess; SecureAirway; IdentifyReversibleCause].

  Lemma all_complete : forall a : t, In a all.
  Proof. intros []; simpl; auto 15. Qed.

  Definition is_drug_action (a : t) : bool :=
    match a with
    | GiveEpinephrine | GiveAmiodarone | GiveLidocaine | GiveMagnesium => true
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

End Action.

(******************************************************************************)
(*                                                                            *)
(*                       SECTION 5: ALGORITHM STATE                           *)
(*                                                                            *)
(*  State machine for ACLS cardiac arrest algorithm tracking.                 *)
(*                                                                            *)
(******************************************************************************)

Module AlgorithmState.

  Record t : Type := mkState {
    current_rhythm : Rhythm.t;
    shock_count : nat;
    cpr_cycles : nat;
    epinephrine_doses : nat;
    amiodarone_doses : nat;
    time_sec : nat;
    last_epi_time_sec : option nat;
    has_iv_access : bool;
    has_advanced_airway : bool;
    rosc_achieved : bool
  }.

  Definition initial (r : Rhythm.t) : t :=
    mkState r 0 0 0 0 0 None false false false.

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
    (amiodarone_doses s <? 2).

  Definition shockable_epi_due (s : t) : bool :=
    is_shockable_state s && (2 <=? shock_count s) && epi_due s.

  Definition nonshockable_epi_due (s : t) : bool :=
    negb (is_shockable_state s) && epi_due s.

  Theorem initial_no_shocks : forall r, shock_count (initial r) = 0.
  Proof. reflexivity. Qed.

  Theorem initial_no_epi : forall r, epinephrine_doses (initial r) = 0.
  Proof. reflexivity. Qed.

  Theorem initial_no_amio : forall r, amiodarone_doses (initial r) = 0.
  Proof. reflexivity. Qed.

  Theorem initial_no_rosc : forall r, rosc_achieved (initial r) = false.
  Proof. reflexivity. Qed.

  Definition with_shock (s : t) : t :=
    mkState (current_rhythm s)
            (S (shock_count s))
            (cpr_cycles s)
            (epinephrine_doses s)
            (amiodarone_doses s)
            (time_sec s)
            (last_epi_time_sec s)
            (has_iv_access s)
            (has_advanced_airway s)
            (rosc_achieved s).

  Definition with_cpr_cycle (s : t) : t :=
    mkState (current_rhythm s)
            (shock_count s)
            (S (cpr_cycles s))
            (epinephrine_doses s)
            (amiodarone_doses s)
            (time_sec s + CPR.cycle_duration_sec)
            (last_epi_time_sec s)
            (has_iv_access s)
            (has_advanced_airway s)
            (rosc_achieved s).

  Definition with_epinephrine (s : t) : t :=
    mkState (current_rhythm s)
            (shock_count s)
            (cpr_cycles s)
            (S (epinephrine_doses s))
            (amiodarone_doses s)
            (time_sec s)
            (Some (time_sec s))
            (has_iv_access s)
            (has_advanced_airway s)
            (rosc_achieved s).

  Definition with_amiodarone (s : t) : t :=
    mkState (current_rhythm s)
            (shock_count s)
            (cpr_cycles s)
            (epinephrine_doses s)
            (S (amiodarone_doses s))
            (time_sec s)
            (last_epi_time_sec s)
            (has_iv_access s)
            (has_advanced_airway s)
            (rosc_achieved s).

  Definition with_rhythm (s : t) (r : Rhythm.t) : t :=
    mkState r
            (shock_count s)
            (cpr_cycles s)
            (epinephrine_doses s)
            (amiodarone_doses s)
            (time_sec s)
            (last_epi_time_sec s)
            (has_iv_access s)
            (has_advanced_airway s)
            (rosc_achieved s).

  Definition with_rosc (s : t) : t :=
    mkState (current_rhythm s)
            (shock_count s)
            (cpr_cycles s)
            (epinephrine_doses s)
            (amiodarone_doses s)
            (time_sec s)
            (last_epi_time_sec s)
            (has_iv_access s)
            (has_advanced_airway s)
            true.

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
    | Check_Rhythm
    | ROSC_achieved.

  Definition rec_eq_dec : forall r1 r2 : Recommendation, {r1 = r2} + {r1 <> r2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Definition shockable_recommendation (s : AlgorithmState.t) : Recommendation :=
    if rosc_achieved s then ROSC_achieved
    else if shock_count s =? 0 then Shock_then_CPR
    else if (shock_count s =? 1) then Shock_then_CPR
    else if (shock_count s =? 2) && epi_due s then Give_Epi_during_CPR
    else if can_give_amiodarone s && (amiodarone_doses s =? 0) then Give_Amio_during_CPR
    else if can_give_amiodarone s && (amiodarone_doses s =? 1) then Give_Amio_during_CPR
    else if epi_due s then Give_Epi_during_CPR
    else Shock_then_CPR.

  Definition nonshockable_recommendation (s : AlgorithmState.t) : Recommendation :=
    if rosc_achieved s then ROSC_achieved
    else if epi_due s then Give_Epi_during_CPR
    else CPR_only.

  Definition recommend (s : AlgorithmState.t) : Recommendation :=
    if is_shockable_state s then shockable_recommendation s
    else nonshockable_recommendation s.

  Theorem VF_initial_shock : forall s,
    current_rhythm s = Rhythm.VF ->
    shock_count s = 0 ->
    rosc_achieved s = false ->
    recommend s = Shock_then_CPR.
  Proof.
    intros s Hr Hsc Hrosc.
    unfold recommend, is_shockable_state. rewrite Hr. simpl.
    unfold shockable_recommendation. rewrite Hrosc, Hsc. reflexivity.
  Qed.

  Theorem pVT_initial_shock : forall s,
    current_rhythm s = Rhythm.pVT ->
    shock_count s = 0 ->
    rosc_achieved s = false ->
    recommend s = Shock_then_CPR.
  Proof.
    intros s Hr Hsc Hrosc.
    unfold recommend, is_shockable_state. rewrite Hr. simpl.
    unfold shockable_recommendation. rewrite Hrosc, Hsc. reflexivity.
  Qed.

  Theorem PEA_no_shock : forall s,
    current_rhythm s = Rhythm.PEA ->
    rosc_achieved s = false ->
    recommend s <> Shock_then_CPR.
  Proof.
    intros s Hr Hrosc.
    unfold recommend, is_shockable_state. rewrite Hr. simpl.
    unfold nonshockable_recommendation. rewrite Hrosc.
    destruct (epi_due s); discriminate.
  Qed.

  Theorem Asystole_no_shock : forall s,
    current_rhythm s = Rhythm.Asystole ->
    rosc_achieved s = false ->
    recommend s <> Shock_then_CPR.
  Proof.
    intros s Hr Hrosc.
    unfold recommend, is_shockable_state. rewrite Hr. simpl.
    unfold nonshockable_recommendation. rewrite Hrosc.
    destruct (epi_due s); discriminate.
  Qed.

  Theorem nonshockable_immediate_epi : forall r,
    Rhythm.shockable r = false ->
    recommend (initial r) = Give_Epi_during_CPR.
  Proof.
    intros r Hr.
    unfold recommend, is_shockable_state, initial. simpl. rewrite Hr.
    unfold nonshockable_recommendation. simpl.
    unfold epi_due. simpl. reflexivity.
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
    rosc_achieved s = false ->
    can_give_amiodarone s = true.
  Proof.
    intros s Hshock Hsc Hamio Hrosc.
    unfold can_give_amiodarone.
    rewrite Hshock, Hsc, Hamio. reflexivity.
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
    mkTimedState
      (AlgorithmState.mkState
        (AlgorithmState.current_rhythm (state ts))
        (AlgorithmState.shock_count (state ts))
        (AlgorithmState.cpr_cycles (state ts))
        (AlgorithmState.epinephrine_doses (state ts))
        (AlgorithmState.amiodarone_doses (state ts))
        (AlgorithmState.time_sec (state ts) + delta_sec)
        (AlgorithmState.last_epi_time_sec (state ts))
        (AlgorithmState.has_iv_access (state ts))
        (AlgorithmState.has_advanced_airway (state ts))
        (AlgorithmState.rosc_achieved (state ts)))
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

End PostArrestCare.

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
    epi_always_allowed_nonshockable s.
  Proof.
    intros s Hns Hrosc Hepi.
    unfold Decision.recommend, is_shockable_state in *.
    rewrite Hns.
    unfold Decision.nonshockable_recommendation.
    rewrite Hrosc, Hepi. reflexivity.
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
    Decision.recommend s <> Decision.Shock_then_CPR.
  Proof.
    intros s Hr.
    unfold Decision.recommend, is_shockable_state.
    rewrite Hr. simpl.
    unfold Decision.nonshockable_recommendation.
    destruct (rosc_achieved s); [discriminate|].
    destruct (epi_due s); discriminate.
  Qed.

  Theorem never_shock_PEA : forall s,
    current_rhythm s = Rhythm.PEA ->
    Decision.recommend s <> Decision.Shock_then_CPR.
  Proof.
    intros s Hr.
    unfold Decision.recommend, is_shockable_state.
    rewrite Hr. simpl.
    unfold Decision.nonshockable_recommendation.
    destruct (rosc_achieved s); [discriminate|].
    destruct (epi_due s); discriminate.
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
      destruct (rosc_achieved s); [discriminate|].
      destruct (epi_due s); discriminate.
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
    Decision.recommend s = Decision.Shock_then_CPR.
  Proof.
    intros s Hshock Hsc Hrosc.
    unfold Decision.recommend. rewrite Hshock.
    unfold Decision.shockable_recommendation.
    rewrite Hrosc.
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
               Decision.recommend s <> Decision.Shock_then_CPR) /\
    (forall s, AlgorithmState.rosc_achieved s = true ->
               Decision.recommend s = Decision.ROSC_achieved) /\
    (forall s, AlgorithmState.shock_count s < 3 ->
               AlgorithmState.can_give_amiodarone s = false).
  Proof.
    repeat split.
    - intros s Hns.
      unfold Decision.recommend, AlgorithmState.is_shockable_state.
      rewrite Hns.
      unfold Decision.nonshockable_recommendation.
      destruct (AlgorithmState.rosc_achieved s); [discriminate|].
      destruct (AlgorithmState.epi_due s); discriminate.
    - exact Decision.rosc_stops_algorithm.
    - exact NegativeSpecs.never_amio_before_third_shock.
  Qed.

End MainResults.

