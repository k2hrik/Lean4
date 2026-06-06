import Switch13Core
/-
  Switch13Reachability.lean

  Standalone Lean artifact, part 2 of 3.

  This file adds the finite-state search layer.  Starting from an odd natural
  number, it constructs the initial finite state, follows the checked transition
  system, and reaches the point where one row of the public switch table is
  selected.
-/
def c6Residue (m q r : Nat) : Prop :=
  Nat.ModEq m q r
def c6SetDisjoint {α : Type} (A B : Set α) : Prop :=
  ∀ x, x ∈ A → x ∈ B → False
structure C6L1R1NormalForm (q : Nat) where
  u : Nat
  q_eq : q = 1 + 4 * u
theorem c6_l1r1_c7_next_valuation_template (u : Nat) :
    c3V2 (2 * (3 * u + 1)) = 1 + c3V2 (3 * u + 1) :=
  c7_c6_l1r1_next_valuation_template u
inductive C6L1R1NextRegime where
  | next1
  | next2
  | nextGe3
  deriving DecidableEq
def c6L1R1RegimeResidue : C6L1R1NextRegime → Nat
  | .next1 => 1
  | .next2 => 13
  | .nextGe3 => 5
def c6L1R1RegimeModulus : C6L1R1NextRegime → Nat
  | .next1 => 8
  | .next2 => 16
  | .nextGe3 => 16
def c6L1R1RegimeContains (regime : C6L1R1NextRegime) (q : Nat) : Prop :=
  Nat.ModEq (c6L1R1RegimeModulus regime) q (c6L1R1RegimeResidue regime)
theorem c6_l1r1_next1_residue_of_even_u
    (q u k : Nat) (hq : q = 1 + 4 * u) (hu : u = 2 * k) :
    Nat.ModEq 8 q 1 := by
  subst q
  subst u
  exact Nat.ModEq.symm (Nat.modEq_iff_dvd.mpr (by use k; omega))
theorem c6_l1r1_even_u_of_next1_residue
    (q u : Nat) (hq : q = 1 + 4 * u) (hres : Nat.ModEq 8 q 1) :
    u % 2 = 0 := by
  subst q
  have hcancel : Nat.ModEq 8 (1 + 4 * u) (1 + 0) := by simpa using hres
  have hu4 : Nat.ModEq 8 (4 * u) 0 :=
    Nat.ModEq.add_left_cancel' 1 hcancel
  have hrewrite : Nat.ModEq (4 * 2) (4 * u) (4 * 0) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hu4
  have hu2 : Nat.ModEq 2 u 0 :=
    Nat.ModEq.mul_left_cancel' (by norm_num : 4 ≠ 0) hrewrite
  unfold Nat.ModEq at hu2
  simpa using hu2
theorem c6_l1r1_next2_residue_of_u_mod4_3
    (q u : Nat) (hq : q = 1 + 4 * u) (hu : Nat.ModEq 4 u 3) :
    Nat.ModEq 16 q 13 := by
  subst q
  have hmul : Nat.ModEq 16 (4 * u) (4 * 3) := by
    have hraw : Nat.ModEq (4 * 4) (4 * u) (4 * 3) :=
      Nat.ModEq.mul_left' 4 hu
    simpa using hraw
  have hadd := Nat.ModEq.add_left 1 hmul
  simpa using hadd
theorem c6_l1r1_u_mod4_3_of_next2_residue
    (q u : Nat) (hq : q = 1 + 4 * u) (hres : Nat.ModEq 16 q 13) :
    Nat.ModEq 4 u 3 := by
  subst q
  have h13 : Nat.ModEq 16 (1 + 4 * u) (1 + 12) := by simpa using hres
  have hcancel : Nat.ModEq 16 (4 * u) 12 :=
    Nat.ModEq.add_left_cancel' 1 h13
  have hrewrite : Nat.ModEq (4 * 4) (4 * u) (4 * 3) := by
    simpa using hcancel
  exact Nat.ModEq.mul_left_cancel' (by norm_num : 4 ≠ 0) hrewrite
theorem c6_l1r1_next_ge3_residue_of_u_mod4_1
    (q u : Nat) (hq : q = 1 + 4 * u) (hu : Nat.ModEq 4 u 1) :
    Nat.ModEq 16 q 5 := by
  subst q
  have hmul : Nat.ModEq 16 (4 * u) (4 * 1) := by
    have hraw : Nat.ModEq (4 * 4) (4 * u) (4 * 1) :=
      Nat.ModEq.mul_left' 4 hu
    simpa using hraw
  have hadd := Nat.ModEq.add_left 1 hmul
  simpa using hadd
theorem c6_l1r1_u_mod4_1_of_next_ge3_residue
    (q u : Nat) (hq : q = 1 + 4 * u) (hres : Nat.ModEq 16 q 5) :
    Nat.ModEq 4 u 1 := by
  subst q
  have h5 : Nat.ModEq 16 (1 + 4 * u) (1 + 4) := by simpa using hres
  have hcancel : Nat.ModEq 16 (4 * u) 4 :=
    Nat.ModEq.add_left_cancel' 1 h5
  have hrewrite : Nat.ModEq (4 * 4) (4 * u) (4 * 1) := by
    simpa using hcancel
  exact Nat.ModEq.mul_left_cancel' (by norm_num : 4 ≠ 0) hrewrite
theorem c6_l1r1_regimes_pairwise_disjoint :
    ∀ r s, r ≠ s →
      c6SetDisjoint
        {q | c6L1R1RegimeContains r q}
        {q | c6L1R1RegimeContains s q} := by
  intro r s hrs q hq hrq
  cases r <;> cases s <;> try contradiction
  · unfold c6L1R1RegimeContains c6L1R1RegimeModulus c6L1R1RegimeResidue at hq hrq
    have hq16 : Nat.ModEq 8 q 13 := Nat.ModEq.of_dvd (by norm_num : 8 ∣ 16) hrq
    unfold Nat.ModEq at hq hq16
    norm_num at hq hq16
    omega
  · unfold c6L1R1RegimeContains c6L1R1RegimeModulus c6L1R1RegimeResidue at hq hrq
    have hq16 : Nat.ModEq 8 q 5 := Nat.ModEq.of_dvd (by norm_num : 8 ∣ 16) hrq
    unfold Nat.ModEq at hq hq16
    norm_num at hq hq16
    omega
  · unfold c6L1R1RegimeContains c6L1R1RegimeModulus c6L1R1RegimeResidue at hq hrq
    have hq8 : Nat.ModEq 8 q 13 := Nat.ModEq.of_dvd (by norm_num : 8 ∣ 16) hq
    unfold Nat.ModEq at hq8 hrq
    norm_num at hq8 hrq
    omega
  · unfold c6L1R1RegimeContains c6L1R1RegimeModulus c6L1R1RegimeResidue at hq hrq
    unfold Nat.ModEq at hq hrq
    norm_num at hq hrq
    omega
  · unfold c6L1R1RegimeContains c6L1R1RegimeModulus c6L1R1RegimeResidue at hq hrq
    have hq8 : Nat.ModEq 8 q 5 := Nat.ModEq.of_dvd (by norm_num : 8 ∣ 16) hq
    unfold Nat.ModEq at hq8 hrq
    norm_num at hq8 hrq
    omega
  · unfold c6L1R1RegimeContains c6L1R1RegimeModulus c6L1R1RegimeResidue at hq hrq
    unfold Nat.ModEq at hq hrq
    norm_num at hq hrq
    omega
theorem c6_l1r1_escape_m_mod16
    (q m : Nat) (hm : m + 1 = 2 * q) (hq : Nat.ModEq 16 q 5) :
    Nat.ModEq 16 m 9 := by
  have h2q : Nat.ModEq 16 (m + 1) (2 * 5) := by
    rw [hm]
    exact Nat.ModEq.mul_left 2 hq
  have htarget : Nat.ModEq 16 (9 + 1) (2 * 5) := by
    norm_num
  exact Nat.ModEq.add_right_cancel' 1 (Nat.ModEq.trans h2q (Nat.ModEq.symm htarget))
structure C6Class9NegativeGapSupport where
  negative_gap : Nat → Prop
  class9_negative :
    ∀ m, Nat.ModEq 16 m 9 → negative_gap m
theorem c6_l1r1_escape_negative_gap
    (support : C6Class9NegativeGapSupport)
    (q m : Nat) (hm : m + 1 = 2 * q) (hq : Nat.ModEq 16 q 5) :
    support.negative_gap m :=
  support.class9_negative m (c6_l1r1_escape_m_mod16 q m hm hq)
structure C6L2R1NormalForm (q : Nat) where
  u : Nat
  q_eq : q = 4 * u + 3
theorem c6_l2r1_c7_next_valuation_template (u : Nat) :
    c3V2 (2 * (9 * u + 7)) = 1 + c3V2 (9 * u + 7) :=
  c7_c6_l2r1_next_valuation_template u
inductive C6L2R1NextRegime where
  | next1
  | next2
  | nextGe3
  deriving DecidableEq
def c6L2R1RegimeResidue : C6L2R1NextRegime → Nat
  | .next1 => 3
  | .next2 => 15
  | .nextGe3 => 7
def c6L2R1RegimeModulus : C6L2R1NextRegime → Nat
  | .next1 => 8
  | .next2 => 16
  | .nextGe3 => 16
def c6L2R1RegimeContains (regime : C6L2R1NextRegime) (q : Nat) : Prop :=
  Nat.ModEq (c6L2R1RegimeModulus regime) q (c6L2R1RegimeResidue regime)
theorem c6_l2r1_next1_residue_of_even_u
    (q u k : Nat) (hq : q = 4 * u + 3) (hu : u = 2 * k) :
    Nat.ModEq 8 q 3 := by
  subst q
  subst u
  have hmul : Nat.ModEq 8 (4 * (2 * k)) 0 := by
    exact Nat.ModEq.symm (Nat.modEq_iff_dvd.mpr (by use k; omega))
  have hadd := Nat.ModEq.add_right 3 hmul
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hadd
theorem c6_l2r1_even_u_of_next1_residue
    (q u : Nat) (hq : q = 4 * u + 3) (hres : Nat.ModEq 8 q 3) :
    u % 2 = 0 := by
  subst q
  have hcancel : Nat.ModEq 8 (4 * u + 3) (0 + 3) := by simpa using hres
  have hu4 : Nat.ModEq 8 (4 * u) 0 :=
    Nat.ModEq.add_right_cancel' 3 hcancel
  have hrewrite : Nat.ModEq (4 * 2) (4 * u) (4 * 0) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hu4
  have hu2 : Nat.ModEq 2 u 0 :=
    Nat.ModEq.mul_left_cancel' (by norm_num : 4 ≠ 0) hrewrite
  unfold Nat.ModEq at hu2
  simpa using hu2
theorem c6_l2r1_next2_residue_of_u_mod4_3
    (q u : Nat) (hq : q = 4 * u + 3) (hu : Nat.ModEq 4 u 3) :
    Nat.ModEq 16 q 15 := by
  subst q
  have hmul : Nat.ModEq 16 (4 * u) (4 * 3) := by
    have hraw : Nat.ModEq (4 * 4) (4 * u) (4 * 3) :=
      Nat.ModEq.mul_left' 4 hu
    simpa using hraw
  have hadd := Nat.ModEq.add_right 3 hmul
  simpa using hadd
theorem c6_l2r1_u_mod4_3_of_next2_residue
    (q u : Nat) (hq : q = 4 * u + 3) (hres : Nat.ModEq 16 q 15) :
    Nat.ModEq 4 u 3 := by
  subst q
  have h15 : Nat.ModEq 16 (4 * u + 3) (12 + 3) := by simpa using hres
  have hcancel : Nat.ModEq 16 (4 * u) 12 :=
    Nat.ModEq.add_right_cancel' 3 h15
  have hrewrite : Nat.ModEq (4 * 4) (4 * u) (4 * 3) := by
    simpa using hcancel
  exact Nat.ModEq.mul_left_cancel' (by norm_num : 4 ≠ 0) hrewrite
theorem c6_l2r1_next_ge3_residue_of_u_mod4_1
    (q u : Nat) (hq : q = 4 * u + 3) (hu : Nat.ModEq 4 u 1) :
    Nat.ModEq 16 q 7 := by
  subst q
  have hmul : Nat.ModEq 16 (4 * u) (4 * 1) := by
    have hraw : Nat.ModEq (4 * 4) (4 * u) (4 * 1) :=
      Nat.ModEq.mul_left' 4 hu
    simpa using hraw
  have hadd := Nat.ModEq.add_right 3 hmul
  simpa using hadd
theorem c6_l2r1_u_mod4_1_of_next_ge3_residue
    (q u : Nat) (hq : q = 4 * u + 3) (hres : Nat.ModEq 16 q 7) :
    Nat.ModEq 4 u 1 := by
  subst q
  have h7 : Nat.ModEq 16 (4 * u + 3) (4 + 3) := by simpa using hres
  have hcancel : Nat.ModEq 16 (4 * u) 4 :=
    Nat.ModEq.add_right_cancel' 3 h7
  have hrewrite : Nat.ModEq (4 * 4) (4 * u) (4 * 1) := by
    simpa using hcancel
  exact Nat.ModEq.mul_left_cancel' (by norm_num : 4 ≠ 0) hrewrite
theorem c6_l2r1_regimes_pairwise_disjoint :
    ∀ r s, r ≠ s →
      c6SetDisjoint
        {q | c6L2R1RegimeContains r q}
        {q | c6L2R1RegimeContains s q} := by
  intro r s hrs q hq hrq
  cases r <;> cases s <;> try contradiction
  · unfold c6L2R1RegimeContains c6L2R1RegimeModulus c6L2R1RegimeResidue at hq hrq
    have hq8 : Nat.ModEq 8 q 15 := Nat.ModEq.of_dvd (by norm_num : 8 ∣ 16) hrq
    unfold Nat.ModEq at hq hq8
    norm_num at hq hq8
    omega
  · unfold c6L2R1RegimeContains c6L2R1RegimeModulus c6L2R1RegimeResidue at hq hrq
    have hq8 : Nat.ModEq 8 q 7 := Nat.ModEq.of_dvd (by norm_num : 8 ∣ 16) hrq
    unfold Nat.ModEq at hq hq8
    norm_num at hq hq8
    omega
  · unfold c6L2R1RegimeContains c6L2R1RegimeModulus c6L2R1RegimeResidue at hq hrq
    have hq8 : Nat.ModEq 8 q 15 := Nat.ModEq.of_dvd (by norm_num : 8 ∣ 16) hq
    unfold Nat.ModEq at hq8 hrq
    norm_num at hq8 hrq
    omega
  · unfold c6L2R1RegimeContains c6L2R1RegimeModulus c6L2R1RegimeResidue at hq hrq
    unfold Nat.ModEq at hq hrq
    norm_num at hq hrq
    omega
  · unfold c6L2R1RegimeContains c6L2R1RegimeModulus c6L2R1RegimeResidue at hq hrq
    have hq8 : Nat.ModEq 8 q 7 := Nat.ModEq.of_dvd (by norm_num : 8 ∣ 16) hq
    unfold Nat.ModEq at hq8 hrq
    norm_num at hq8 hrq
    omega
  · unfold c6L2R1RegimeContains c6L2R1RegimeModulus c6L2R1RegimeResidue at hq hrq
    unfold Nat.ModEq at hq hrq
    norm_num at hq hrq
    omega
theorem c6_l2r1_gap_positive_power_L1 :
    3 ^ 1 < 2 ^ (1 + 1) := by
  norm_num
theorem c6_pow_two_lt_three_from_two (k : Nat) :
    2 ^ (k + 3) < 3 ^ (k + 2) := by
  induction k with
  | zero =>
      norm_num
  | succ k ih =>
      rw [show k + 1 + 3 = (k + 3) + 1 by omega]
      rw [show k + 1 + 2 = (k + 2) + 1 by omega]
      rw [pow_succ, pow_succ]
      have h2 : 2 ^ (k + 3) * 2 < 3 ^ (k + 2) * 2 :=
        Nat.mul_lt_mul_of_pos_right ih (by norm_num)
      have h3 : 3 ^ (k + 2) * 2 < 3 ^ (k + 2) * 3 := by
        have hpos : 0 < 3 ^ (k + 2) := pow_pos (by norm_num) _
        nlinarith
      exact lt_trans h2 h3
theorem c6_l2r1_gap_negative_power_of_ge2
    (Lnext : Nat) (hL : 2 <= Lnext) :
    2 ^ (Lnext + 1) < 3 ^ Lnext := by
  obtain ⟨k, hk⟩ : ∃ k, Lnext = k + 2 := ⟨Lnext - 2, by omega⟩
  subst Lnext
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    c6_pow_two_lt_three_from_two k
structure C6LNext1NormalForm (q : Nat) where
  t : Nat
  q_eq : q = 1 + 8 * t
  q1 : Nat
  q1_eq : q1 = 6 * t + 1
theorem c6_lnext1_q1_formula
    (q t q1 : Nat) (hq : q = 1 + 8 * t) (hq1 : q1 = 6 * t + 1) :
    q1 = (3 * q + 1) / 4 := by
  subst q
  subst q1
  rw [show 3 * (1 + 8 * t) + 1 = 4 * (6 * t + 1) by omega]
  have hdiv : 4 * (6 * t + 1) / 4 = 6 * t + 1 :=
    Nat.mul_div_right (6 * t + 1) (by norm_num : 0 < 4)
  rw [hdiv]
theorem c6_lnext1_resonance1_residue_of_even_t
    (q t k : Nat) (hq : q = 1 + 8 * t) (ht : t = 2 * k) :
    Nat.ModEq 16 q 1 := by
  subst q
  subst t
  exact Nat.ModEq.symm (Nat.modEq_iff_dvd.mpr (by use k; omega))
theorem c6_lnext1_even_t_of_resonance1_residue
    (q t : Nat) (hq : q = 1 + 8 * t) (hres : Nat.ModEq 16 q 1) :
    t % 2 = 0 := by
  subst q
  have hcancel : Nat.ModEq 16 (1 + 8 * t) (1 + 0) := by simpa using hres
  have ht8 : Nat.ModEq 16 (8 * t) 0 :=
    Nat.ModEq.add_left_cancel' 1 hcancel
  have hrewrite : Nat.ModEq (8 * 2) (8 * t) (8 * 0) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using ht8
  have ht2 : Nat.ModEq 2 t 0 :=
    Nat.ModEq.mul_left_cancel' (by norm_num : 8 ≠ 0) hrewrite
  unfold Nat.ModEq at ht2
  simpa using ht2
theorem c6_lnext1_resonance_ge2_residue_of_odd_t
    (q t : Nat) (hq : q = 1 + 8 * t) (ht : Nat.ModEq 2 t 1) :
    Nat.ModEq 16 q 9 := by
  subst q
  have hmul : Nat.ModEq 16 (8 * t) (8 * 1) := by
    have hraw : Nat.ModEq (8 * 2) (8 * t) (8 * 1) :=
      Nat.ModEq.mul_left' 8 ht
    simpa using hraw
  have hadd := Nat.ModEq.add_left 1 hmul
  simpa using hadd
theorem c6_lnext1_odd_t_of_resonance_ge2_residue
    (q t : Nat) (hq : q = 1 + 8 * t) (hres : Nat.ModEq 16 q 9) :
    Nat.ModEq 2 t 1 := by
  subst q
  have h9 : Nat.ModEq 16 (1 + 8 * t) (1 + 8) := by simpa using hres
  have hcancel : Nat.ModEq 16 (8 * t) 8 :=
    Nat.ModEq.add_left_cancel' 1 h9
  have hrewrite : Nat.ModEq (8 * 2) (8 * t) (8 * 1) := by
    simpa using hcancel
  exact Nat.ModEq.mul_left_cancel' (by norm_num : 8 ≠ 0) hrewrite
theorem c6_lnext1_L2_eq1_residue_of_even_v
    (q v k : Nat) (hq : q = 1 + 16 * v) (hv : v = 2 * k) :
    Nat.ModEq 32 q 1 := by
  subst q
  subst v
  exact Nat.ModEq.symm (Nat.modEq_iff_dvd.mpr (by use k; omega))
theorem c6_lnext1_even_v_of_L2_eq1_residue
    (q v : Nat) (hq : q = 1 + 16 * v) (hres : Nat.ModEq 32 q 1) :
    v % 2 = 0 := by
  subst q
  have hcancel : Nat.ModEq 32 (1 + 16 * v) (1 + 0) := by simpa using hres
  have hv16 : Nat.ModEq 32 (16 * v) 0 :=
    Nat.ModEq.add_left_cancel' 1 hcancel
  have hrewrite : Nat.ModEq (16 * 2) (16 * v) (16 * 0) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hv16
  have hv2 : Nat.ModEq 2 v 0 :=
    Nat.ModEq.mul_left_cancel' (by norm_num : 16 ≠ 0) hrewrite
  unfold Nat.ModEq at hv2
  simpa using hv2
theorem c6_lnext1_L2_eq2_residue_of_v_mod4_1
    (q v : Nat) (hq : q = 1 + 16 * v) (hv : Nat.ModEq 4 v 1) :
    Nat.ModEq 64 q 17 := by
  subst q
  have hmul : Nat.ModEq 64 (16 * v) (16 * 1) := by
    have hraw : Nat.ModEq (16 * 4) (16 * v) (16 * 1) :=
      Nat.ModEq.mul_left' 16 hv
    simpa using hraw
  have hadd := Nat.ModEq.add_left 1 hmul
  simpa using hadd
theorem c6_lnext1_v_mod4_1_of_L2_eq2_residue
    (q v : Nat) (hq : q = 1 + 16 * v) (hres : Nat.ModEq 64 q 17) :
    Nat.ModEq 4 v 1 := by
  subst q
  have h17 : Nat.ModEq 64 (1 + 16 * v) (1 + 16) := by simpa using hres
  have hcancel : Nat.ModEq 64 (16 * v) 16 :=
    Nat.ModEq.add_left_cancel' 1 h17
  have hrewrite : Nat.ModEq (16 * 4) (16 * v) (16 * 1) := by
    simpa using hcancel
  exact Nat.ModEq.mul_left_cancel' (by norm_num : 16 ≠ 0) hrewrite
theorem c6_lnext1_L2_ge3_residue_of_v_mod4_3
    (q v : Nat) (hq : q = 1 + 16 * v) (hv : Nat.ModEq 4 v 3) :
    Nat.ModEq 64 q 49 := by
  subst q
  have hmul : Nat.ModEq 64 (16 * v) (16 * 3) := by
    have hraw : Nat.ModEq (16 * 4) (16 * v) (16 * 3) :=
      Nat.ModEq.mul_left' 16 hv
    simpa using hraw
  have hadd := Nat.ModEq.add_left 1 hmul
  simpa using hadd
theorem c6_lnext1_v_mod4_3_of_L2_ge3_residue
    (q v : Nat) (hq : q = 1 + 16 * v) (hres : Nat.ModEq 64 q 49) :
    Nat.ModEq 4 v 3 := by
  subst q
  have h49 : Nat.ModEq 64 (1 + 16 * v) (1 + 48) := by simpa using hres
  have hcancel : Nat.ModEq 64 (16 * v) 48 :=
    Nat.ModEq.add_left_cancel' 1 h49
  have hrewrite : Nat.ModEq (16 * 4) (16 * v) (16 * 3) := by
    simpa using hcancel
  exact Nat.ModEq.mul_left_cancel' (by norm_num : 16 ≠ 0) hrewrite
structure C6LNext2NormalForm (q : Nat) where
  t : Nat
  q_eq : q = 16 * t + 13
  q1 : Nat
  q1_eq : q1 = 6 * t + 5
theorem c6_lnext2_q1_formula
    (q t q1 : Nat) (hq : q = 16 * t + 13) (hq1 : q1 = 6 * t + 5) :
    q1 = (3 * q + 1) / 8 := by
  subst q
  subst q1
  rw [show 3 * (16 * t + 13) + 1 = 8 * (6 * t + 5) by omega]
  have hdiv : 8 * (6 * t + 5) / 8 = 6 * t + 5 :=
    Nat.mul_div_right (6 * t + 5) (by norm_num : 0 < 8)
  rw [hdiv]
theorem c6_lnext2_resonance1_residue_of_even_t
    (q t k : Nat) (hq : q = 16 * t + 13) (ht : t = 2 * k) :
    Nat.ModEq 32 q 13 := by
  subst q
  subst t
  exact Nat.ModEq.symm (Nat.modEq_iff_dvd.mpr (by use k; omega))
theorem c6_lnext2_even_t_of_resonance1_residue
    (q t : Nat) (hq : q = 16 * t + 13) (hres : Nat.ModEq 32 q 13) :
    t % 2 = 0 := by
  subst q
  have h13 : Nat.ModEq 32 (16 * t + 13) (0 + 13) := by simpa using hres
  have hcancel : Nat.ModEq 32 (16 * t) 0 :=
    Nat.ModEq.add_right_cancel' 13 h13
  have hrewrite : Nat.ModEq (16 * 2) (16 * t) (16 * 0) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcancel
  have ht2 : Nat.ModEq 2 t 0 :=
    Nat.ModEq.mul_left_cancel' (by norm_num : 16 ≠ 0) hrewrite
  unfold Nat.ModEq at ht2
  simpa using ht2
theorem c6_lnext2_resonance2_residue_of_odd_s
    (q s : Nat) (hq : q = 32 * s + 29) (hs : Nat.ModEq 2 s 1) :
    Nat.ModEq 64 q 61 := by
  subst q
  have hmul : Nat.ModEq 64 (32 * s) (32 * 1) := by
    have hraw : Nat.ModEq (32 * 2) (32 * s) (32 * 1) :=
      Nat.ModEq.mul_left' 32 hs
    simpa using hraw
  have hadd := Nat.ModEq.add_right 29 hmul
  simpa using hadd
theorem c6_lnext2_odd_s_of_resonance2_residue
    (q s : Nat) (hq : q = 32 * s + 29) (hres : Nat.ModEq 64 q 61) :
    Nat.ModEq 2 s 1 := by
  subst q
  have h61 : Nat.ModEq 64 (32 * s + 29) (32 + 29) := by simpa using hres
  have hcancel : Nat.ModEq 64 (32 * s) 32 :=
    Nat.ModEq.add_right_cancel' 29 h61
  have hrewrite : Nat.ModEq (32 * 2) (32 * s) (32 * 1) := by
    simpa using hcancel
  exact Nat.ModEq.mul_left_cancel' (by norm_num : 32 ≠ 0) hrewrite
theorem c6_lnext2_resonance_ge3_residue_of_even_s
    (q s k : Nat) (hq : q = 32 * s + 29) (hs : s = 2 * k) :
    Nat.ModEq 64 q 29 := by
  subst q
  subst s
  exact Nat.ModEq.symm (Nat.modEq_iff_dvd.mpr (by use k; omega))
theorem c6_lnext2_even_s_of_resonance_ge3_residue
    (q s : Nat) (hq : q = 32 * s + 29) (hres : Nat.ModEq 64 q 29) :
    s % 2 = 0 := by
  subst q
  have h29 : Nat.ModEq 64 (32 * s + 29) (0 + 29) := by simpa using hres
  have hcancel : Nat.ModEq 64 (32 * s) 0 :=
    Nat.ModEq.add_right_cancel' 29 h29
  have hrewrite : Nat.ModEq (32 * 2) (32 * s) (32 * 0) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcancel
  have hs2 : Nat.ModEq 2 s 0 :=
    Nat.ModEq.mul_left_cancel' (by norm_num : 32 ≠ 0) hrewrite
  unfold Nat.ModEq at hs2
  simpa using hs2
theorem c6_lnext2_L2_eq1_residue_of_odd_v
    (q v : Nat) (hq : q = 32 * v + 13) (hv : Nat.ModEq 2 v 1) :
    Nat.ModEq 64 q 45 := by
  subst q
  have hmul : Nat.ModEq 64 (32 * v) (32 * 1) := by
    have hraw : Nat.ModEq (32 * 2) (32 * v) (32 * 1) :=
      Nat.ModEq.mul_left' 32 hv
    simpa using hraw
  have hadd := Nat.ModEq.add_right 13 hmul
  simpa using hadd
theorem c6_lnext2_odd_v_of_L2_eq1_residue
    (q v : Nat) (hq : q = 32 * v + 13) (hres : Nat.ModEq 64 q 45) :
    Nat.ModEq 2 v 1 := by
  subst q
  have h45 : Nat.ModEq 64 (32 * v + 13) (32 + 13) := by simpa using hres
  have hcancel : Nat.ModEq 64 (32 * v) 32 :=
    Nat.ModEq.add_right_cancel' 13 h45
  have hrewrite : Nat.ModEq (32 * 2) (32 * v) (32 * 1) := by
    simpa using hcancel
  exact Nat.ModEq.mul_left_cancel' (by norm_num : 32 ≠ 0) hrewrite
theorem c6_lnext2_L2_eq2_residue_of_odd_w
    (q w : Nat) (hq : q = 64 * w + 13) (hw : Nat.ModEq 2 w 1) :
    Nat.ModEq 128 q 77 := by
  subst q
  have hmul : Nat.ModEq 128 (64 * w) (64 * 1) := by
    have hraw : Nat.ModEq (64 * 2) (64 * w) (64 * 1) :=
      Nat.ModEq.mul_left' 64 hw
    simpa using hraw
  have hadd := Nat.ModEq.add_right 13 hmul
  simpa using hadd
theorem c6_lnext2_odd_w_of_L2_eq2_residue
    (q w : Nat) (hq : q = 64 * w + 13) (hres : Nat.ModEq 128 q 77) :
    Nat.ModEq 2 w 1 := by
  subst q
  have h77 : Nat.ModEq 128 (64 * w + 13) (64 + 13) := by simpa using hres
  have hcancel : Nat.ModEq 128 (64 * w) 64 :=
    Nat.ModEq.add_right_cancel' 13 h77
  have hrewrite : Nat.ModEq (64 * 2) (64 * w) (64 * 1) := by
    simpa using hcancel
  exact Nat.ModEq.mul_left_cancel' (by norm_num : 64 ≠ 0) hrewrite
theorem c6_lnext2_L2_ge3_residue_of_even_w
    (q w k : Nat) (hq : q = 64 * w + 13) (hw : w = 2 * k) :
    Nat.ModEq 128 q 13 := by
  subst q
  subst w
  exact Nat.ModEq.symm (Nat.modEq_iff_dvd.mpr (by use k; omega))
theorem c6_lnext2_even_w_of_L2_ge3_residue
    (q w : Nat) (hq : q = 64 * w + 13) (hres : Nat.ModEq 128 q 13) :
    w % 2 = 0 := by
  subst q
  have h13 : Nat.ModEq 128 (64 * w + 13) (0 + 13) := by simpa using hres
  have hcancel : Nat.ModEq 128 (64 * w) 0 :=
    Nat.ModEq.add_right_cancel' 13 h13
  have hrewrite : Nat.ModEq (64 * 2) (64 * w) (64 * 0) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcancel
  have hw2 : Nat.ModEq 2 w 0 :=
    Nat.ModEq.mul_left_cancel' (by norm_num : 64 ≠ 0) hrewrite
  unfold Nat.ModEq at hw2
  simpa using hw2
structure C6LNext1Mod256ChildSplit where
  parent64 : Nat
  childBase : Nat
  parent256 : Fin 4 → Nat
  child64 : Fin 4 → Nat
  parent256_eq : ∀ i : Fin 4, parent256 i = parent64 + 64 * (i : Nat)
  child64_eq : ∀ i : Fin 4, child64 i = (childBase + 48 * (i : Nat)) % 64
theorem c6_lnext1_child_affine_formula
    (u b c q q1 : Nat) (hb : 3 * b + 1 = 4 * c)
    (hq : q = 64 * u + b) (hq1 : q1 = 48 * u + c) :
    q1 = (3 * q + 1) / 4 := by
  subst q
  subst q1
  have hnum : 3 * (64 * u + b) + 1 = 4 * (48 * u + c) := by
    nlinarith
  rw [hnum]
  have hdiv : 4 * (48 * u + c) / 4 = 48 * u + c :=
    Nat.mul_div_right (48 * u + c) (by norm_num : 0 < 4)
  rw [hdiv]
theorem c6_lnext1_parent_mod256_of_u_mod4
    (u b i : Nat) (hu : Nat.ModEq 4 u i) :
    Nat.ModEq 256 (64 * u + b) (b + 64 * i) := by
  have hmul : Nat.ModEq 256 (64 * u) (64 * i) := by
    have hraw : Nat.ModEq (64 * 4) (64 * u) (64 * i) :=
      Nat.ModEq.mul_left' 64 hu
    simpa using hraw
  have hadd := Nat.ModEq.add_right b hmul
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hadd
theorem c6_lnext1_child_mod64_of_u_mod4
    (u c i : Nat) (hu : Nat.ModEq 4 u i) :
    Nat.ModEq 64 (48 * u + c) ((c + 48 * i) % 64) := by
  have hmul : Nat.ModEq 64 (48 * u) (48 * i) := by
    have hraw : Nat.ModEq (16 * 4) (16 * (3 * u)) (16 * (3 * i)) := by
      exact Nat.ModEq.mul_left' 16 (Nat.ModEq.mul_left 3 hu)
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hraw
  have hadd := Nat.ModEq.add_right c hmul
  have hmod : Nat.ModEq 64 (48 * i + c) ((c + 48 * i) % 64) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (Nat.mod_modEq (c + 48 * i) 64).symm
  exact Nat.ModEq.trans
    (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hadd)
    (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hmod)
theorem c6_lnext1_parent256_children_disjoint
    (b : Nat) (hb : b < 64) :
    ∀ i j : Fin 4, i ≠ j →
      c6SetDisjoint
        {q | Nat.ModEq 256 q (b + 64 * (i : Nat))}
        {q | Nat.ModEq 256 q (b + 64 * (j : Nat))} := by
  intro i j hij q hiq hjq
  unfold Nat.ModEq at hiq hjq
  have hlt_i : (i : Nat) < 4 := i.isLt
  have hlt_j : (j : Nat) < 4 := j.isLt
  have hbound_i : b + 64 * (i : Nat) < 256 := by omega
  have hbound_j : b + 64 * (j : Nat) < 256 := by omega
  rw [Nat.mod_eq_of_lt hbound_i] at hiq
  rw [Nat.mod_eq_of_lt hbound_j] at hjq
  have heq : b + 64 * (i : Nat) = b + 64 * (j : Nat) := by
    rw [← hiq, ← hjq]
  have hlin : (i : Nat) = (j : Nat) := by
    omega
  exact hij (Fin.ext hlin)
theorem c6_lnext1_child_formula_parent1
    (u q q1 : Nat) (hq : q = 64 * u + 1) (hq1 : q1 = 48 * u + 1) :
    q1 = (3 * q + 1) / 4 :=
  c6_lnext1_child_affine_formula u 1 1 q q1 (by norm_num) hq hq1
def c6_lnext1_split_parent1 : C6LNext1Mod256ChildSplit where
  parent64 := 1
  childBase := 1
  parent256 := fun i => 1 + 64 * (i : Nat)
  child64 := fun i => (1 + 48 * (i : Nat)) % 64
  parent256_eq := by intro i; rfl
  child64_eq := by intro i; rfl
theorem c6_lnext1_parent1_child_mod64_zero :
    (c6_lnext1_split_parent1.child64 0 = 1) := rfl
theorem c6_lnext1_parent1_child_mod64_one :
    (c6_lnext1_split_parent1.child64 1 = 49) := rfl
theorem c6_lnext1_parent1_child_mod64_two :
    (c6_lnext1_split_parent1.child64 2 = 33) := rfl
theorem c6_lnext1_parent1_child_mod64_three :
    (c6_lnext1_split_parent1.child64 3 = 17) := rfl
theorem c6_lnext1_child_formula_parent25
    (u q q1 : Nat) (hq : q = 64 * u + 25) (hq1 : q1 = 48 * u + 19) :
    q1 = (3 * q + 1) / 4 :=
  c6_lnext1_child_affine_formula u 25 19 q q1 (by norm_num) hq hq1
def c6_lnext1_split_parent25 : C6LNext1Mod256ChildSplit where
  parent64 := 25
  childBase := 19
  parent256 := fun i => 25 + 64 * (i : Nat)
  child64 := fun i => (19 + 48 * (i : Nat)) % 64
  parent256_eq := by intro i; rfl
  child64_eq := by intro i; rfl
theorem c6_lnext1_parent25_child_mod64_zero :
    (c6_lnext1_split_parent25.child64 0 = 19) := rfl
theorem c6_lnext1_parent25_child_mod64_one :
    (c6_lnext1_split_parent25.child64 1 = 3) := rfl
theorem c6_lnext1_parent25_child_mod64_two :
    (c6_lnext1_split_parent25.child64 2 = 51) := rfl
theorem c6_lnext1_parent25_child_mod64_three :
    (c6_lnext1_split_parent25.child64 3 = 35) := rfl
theorem c6_lnext1_child_formula_parent41
    (u q q1 : Nat) (hq : q = 64 * u + 41) (hq1 : q1 = 48 * u + 31) :
    q1 = (3 * q + 1) / 4 :=
  c6_lnext1_child_affine_formula u 41 31 q q1 (by norm_num) hq hq1
def c6_lnext1_split_parent41 : C6LNext1Mod256ChildSplit where
  parent64 := 41
  childBase := 31
  parent256 := fun i => 41 + 64 * (i : Nat)
  child64 := fun i => (31 + 48 * (i : Nat)) % 64
  parent256_eq := by intro i; rfl
  child64_eq := by intro i; rfl
theorem c6_lnext1_parent41_child_mod64_zero :
    (c6_lnext1_split_parent41.child64 0 = 31) := rfl
theorem c6_lnext1_parent41_child_mod64_one :
    (c6_lnext1_split_parent41.child64 1 = 15) := rfl
theorem c6_lnext1_parent41_child_mod64_two :
    (c6_lnext1_split_parent41.child64 2 = 63) := rfl
theorem c6_lnext1_parent41_child_mod64_three :
    (c6_lnext1_split_parent41.child64 3 = 47) := rfl
theorem c6_lnext1_parent41_children_mod16
    (i : Fin 4) :
    Nat.ModEq 16 (c6_lnext1_split_parent41.child64 i) 15 := by
  fin_cases i <;> norm_num [c6_lnext1_split_parent41]
theorem c6_lnext1_child_formula_parent57
    (u q q1 : Nat) (hq : q = 64 * u + 57) (hq1 : q1 = 48 * u + 43) :
    q1 = (3 * q + 1) / 4 :=
  c6_lnext1_child_affine_formula u 57 43 q q1 (by norm_num) hq hq1
def c6_lnext1_split_parent57 : C6LNext1Mod256ChildSplit where
  parent64 := 57
  childBase := 43
  parent256 := fun i => 57 + 64 * (i : Nat)
  child64 := fun i => (43 + 48 * (i : Nat)) % 64
  parent256_eq := by intro i; rfl
  child64_eq := by intro i; rfl
theorem c6_lnext1_parent57_child_mod64_zero :
    (c6_lnext1_split_parent57.child64 0 = 43) := rfl
theorem c6_lnext1_parent57_child_mod64_one :
    (c6_lnext1_split_parent57.child64 1 = 27) := rfl
theorem c6_lnext1_parent57_child_mod64_two :
    (c6_lnext1_split_parent57.child64 2 = 11) := rfl
theorem c6_lnext1_parent57_child_mod64_three :
    (c6_lnext1_split_parent57.child64 3 = 59) := rfl
theorem c6_lnext1_parent57_children_mod16
    (i : Fin 4) :
    Nat.ModEq 16 (c6_lnext1_split_parent57.child64 i) 11 := by
  fin_cases i <;> norm_num [c6_lnext1_split_parent57]
theorem c6_lnext1_child_formula_parent33
    (u q q1 : Nat) (hq : q = 64 * u + 33) (hq1 : q1 = 48 * u + 25) :
    q1 = (3 * q + 1) / 4 :=
  c6_lnext1_child_affine_formula u 33 25 q q1 (by norm_num) hq hq1
def c6_lnext1_split_parent33 : C6LNext1Mod256ChildSplit where
  parent64 := 33
  childBase := 25
  parent256 := fun i => 33 + 64 * (i : Nat)
  child64 := fun i => (25 + 48 * (i : Nat)) % 64
  parent256_eq := by intro i; rfl
  child64_eq := by intro i; rfl
theorem c6_lnext1_parent33_child_mod64_zero :
    (c6_lnext1_split_parent33.child64 0 = 25) := rfl
theorem c6_lnext1_parent33_child_mod64_one :
    (c6_lnext1_split_parent33.child64 1 = 9) := rfl
theorem c6_lnext1_parent33_child_mod64_two :
    (c6_lnext1_split_parent33.child64 2 = 57) := rfl
theorem c6_lnext1_parent33_child_mod64_three :
    (c6_lnext1_split_parent33.child64 3 = 41) := rfl
theorem c6_lnext1_parent33_children_mod16
    (i : Fin 4) :
    Nat.ModEq 16 (c6_lnext1_split_parent33.child64 i) 9 := by
  fin_cases i <;> norm_num [c6_lnext1_split_parent33]
theorem c6_lnext1_child_formula_parent9
    (u q q1 : Nat) (hq : q = 64 * u + 9) (hq1 : q1 = 48 * u + 7) :
    q1 = (3 * q + 1) / 4 :=
  c6_lnext1_child_affine_formula u 9 7 q q1 (by norm_num) hq hq1
def c6_lnext1_split_parent9 : C6LNext1Mod256ChildSplit where
  parent64 := 9
  childBase := 7
  parent256 := fun i => 9 + 64 * (i : Nat)
  child64 := fun i => (7 + 48 * (i : Nat)) % 64
  parent256_eq := by intro i; rfl
  child64_eq := by intro i; rfl
theorem c6_lnext1_parent9_child_mod64_zero :
    (c6_lnext1_split_parent9.child64 0 = 7) := rfl
theorem c6_lnext1_parent9_child_mod64_one :
    (c6_lnext1_split_parent9.child64 1 = 55) := rfl
theorem c6_lnext1_parent9_child_mod64_two :
    (c6_lnext1_split_parent9.child64 2 = 39) := rfl
theorem c6_lnext1_parent9_child_mod64_three :
    (c6_lnext1_split_parent9.child64 3 = 23) := rfl
theorem c6_lnext1_parent9_children_mod16
    (i : Fin 4) :
    Nat.ModEq 16 (c6_lnext1_split_parent9.child64 i) 7 := by
  fin_cases i <;> norm_num [c6_lnext1_split_parent9]
structure C6Res3Mod256NormalForm (q : Nat) where
  u : Nat
  q_eq : q = 256 * u + 3
theorem c6_res3_mod256_m1_formula
    (u q m1 : Nat) (hq : q = 256 * u + 3) (hm1 : m1 = 96 * u + 1) :
    m1 = (3 * q - 1) / 8 := by
  subst q
  subst m1
  rw [show 3 * (256 * u + 3) - 1 = 8 * (96 * u + 1) by omega]
  have hdiv : 8 * (96 * u + 1) / 8 = 96 * u + 1 :=
    Nat.mul_div_right (96 * u + 1) (by norm_num : 0 < 8)
  rw [hdiv]
theorem c6_res3_mod256_m1_odd (u : Nat) :
    (96 * u + 1) % 2 = 1 := by
  omega
theorem c6_res3_mod256_q1_formula
    (u m1 q1 : Nat) (hm1 : m1 = 96 * u + 1) (hq1 : q1 = 48 * u + 1) :
    q1 = (m1 + 1) / 2 := by
  subst m1
  subst q1
  rw [show 96 * u + 1 + 1 = 2 * (48 * u + 1) by omega]
  have hdiv : 2 * (48 * u + 1) / 2 = 48 * u + 1 :=
    Nat.mul_div_right (48 * u + 1) (by norm_num : 0 < 2)
  rw [hdiv]
def c6_res3_mod256_immediate_child64 : Fin 4 → Nat :=
  fun i => (1 + 48 * (i : Nat)) % 64
theorem c6_res3_mod256_child_mod64_of_u_mod4
    (u q1 i : Nat) (hq1 : q1 = 48 * u + 1) (hu : Nat.ModEq 4 u i) :
    Nat.ModEq 64 q1 (c6_res3_mod256_immediate_child64 ⟨i % 4, Nat.mod_lt _ (by norm_num)⟩) := by
  subst q1
  have hi : Nat.ModEq 4 i (i % 4) := (Nat.mod_modEq i 4).symm
  have hu' : Nat.ModEq 4 u (i % 4) := Nat.ModEq.trans hu hi
  simpa [c6_res3_mod256_immediate_child64] using
    c6_lnext1_child_mod64_of_u_mod4 u 1 (i % 4) hu'
theorem c6_res3_mod256_child64_zero :
    c6_res3_mod256_immediate_child64 0 = 1 := rfl
theorem c6_res3_mod256_child64_one :
    c6_res3_mod256_immediate_child64 1 = 49 := rfl
theorem c6_res3_mod256_child64_two :
    c6_res3_mod256_immediate_child64 2 = 33 := rfl
theorem c6_res3_mod256_child64_three :
    c6_res3_mod256_immediate_child64 3 = 17 := rfl
theorem c6_res3_mod256_children_mod16
    (i : Fin 4) :
    Nat.ModEq 16 (c6_res3_mod256_immediate_child64 i) 1 := by
  fin_cases i <;> norm_num [c6_res3_mod256_immediate_child64]
inductive C6Res3ImmediateChildKind where
  | recursiveCheap
  | nextLength2
  | nextLengthGe3
  deriving DecidableEq
def c6_res3_mod256_child_kind (i : Fin 4) : C6Res3ImmediateChildKind :=
  match (i : Nat) with
  | 0 => .recursiveCheap
  | 1 => .nextLengthGe3
  | 2 => .recursiveCheap
  | _ => .nextLength2
theorem c6_res3_mod256_recursive_indices :
    (∀ i : Fin 4,
      c6_res3_mod256_child_kind i = C6Res3ImmediateChildKind.recursiveCheap ↔
        (i : Nat) = 0 ∨ (i : Nat) = 2) := by
  intro i
  fin_cases i <;> simp [c6_res3_mod256_child_kind]
theorem c6_res3_mod256_nonrecursive_17 :
    c6_res3_mod256_child_kind 3 = C6Res3ImmediateChildKind.nextLength2 := rfl
theorem c6_res3_mod256_nonrecursive_49 :
    c6_res3_mod256_child_kind 1 = C6Res3ImmediateChildKind.nextLengthGe3 := rfl
def c6_res3_recursive_from_child1 : Fin 4 → Nat :=
  c6_lnext1_split_parent1.child64
def c6_res3_recursive_from_child33 : Fin 4 → Nat :=
  c6_lnext1_split_parent33.child64
def c6_res3_two_generation_recursive_menu : Fin 8 → Nat
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 17
  | ⟨2, _⟩ => 33
  | ⟨3, _⟩ => 49
  | ⟨4, _⟩ => 25
  | ⟨5, _⟩ => 9
  | ⟨6, _⟩ => 57
  | _ => 41
theorem c6_res3_two_generation_recursive_menu_members
    (i : Fin 8) :
    c6_res3_two_generation_recursive_menu i = 1 ∨
    c6_res3_two_generation_recursive_menu i = 9 ∨
    c6_res3_two_generation_recursive_menu i = 25 ∨
    c6_res3_two_generation_recursive_menu i = 33 ∨
    c6_res3_two_generation_recursive_menu i = 41 ∨
    c6_res3_two_generation_recursive_menu i = 57 ∨
    c6_res3_two_generation_recursive_menu i = 17 ∨
    c6_res3_two_generation_recursive_menu i = 49 := by
  fin_cases i <;> simp [c6_res3_two_generation_recursive_menu]
theorem c6_res3_two_generation_recursive_cheap_contained
    (i : Fin 8)
    (hrec : c6_res3_two_generation_recursive_menu i ≠ 17 ∧
      c6_res3_two_generation_recursive_menu i ≠ 49) :
    c6_res3_two_generation_recursive_menu i = 1 ∨
    c6_res3_two_generation_recursive_menu i = 9 ∨
    c6_res3_two_generation_recursive_menu i = 25 ∨
    c6_res3_two_generation_recursive_menu i = 33 ∨
    c6_res3_two_generation_recursive_menu i = 41 ∨
    c6_res3_two_generation_recursive_menu i = 57 := by
  fin_cases i <;> simp [c6_res3_two_generation_recursive_menu] at hrec ⊢
structure C6CheapPrefixNormalForm (n q0 : Nat) where
  k : Nat
  q0_eq : q0 = 1 + 2 ^ (2 * n) * k
  qLast : Nat
  qLast_eq : qLast = 1 + 4 * 3 ^ (n - 1) * k
theorem c6_cheap_prefix_base_residue
    (n q0 : Nat) (N : C6CheapPrefixNormalForm n q0) :
    Nat.ModEq (2 ^ (2 * n)) q0 1 := by
  rw [N.q0_eq]
  exact Nat.ModEq.symm (Nat.modEq_iff_dvd.mpr (by use N.k; omega))
theorem c6_cheap_prefix_step_formula
    (e j k qj qnext : Nat)
    (hqj : qj = 1 + 2 ^ (e + 2) * 3 ^ j * k)
    (hqnext : qnext = 1 + 2 ^ e * 3 ^ (j + 1) * k) :
    qnext = (3 * qj + 1) / 4 := by
  subst qj
  subst qnext
  have hpow2 : 2 ^ (e + 2) = 2 ^ e * 4 := by
    rw [pow_add]
    norm_num
  have hpow3 : 3 ^ (j + 1) = 3 ^ j * 3 := by
    rw [pow_succ]
  rw [hpow2, hpow3]
  have hnum :
      3 * (1 + (2 ^ e * 4) * 3 ^ j * k) + 1 =
        4 * (1 + 2 ^ e * (3 ^ j * 3) * k) := by
    ring
  rw [hnum]
  have hdiv :
      4 * (1 + 2 ^ e * (3 ^ j * 3) * k) / 4 =
        1 + 2 ^ e * (3 ^ j * 3) * k :=
    Nat.mul_div_right (1 + 2 ^ e * (3 ^ j * 3) * k) (by norm_num : 0 < 4)
  rw [hdiv]
theorem c6_cheap_prefix_state_formula_zero
    (n k q0 : Nat) (hq0 : q0 = 1 + 2 ^ (2 * n) * k) :
    q0 = 1 + 2 ^ (2 * n) * 3 ^ 0 * k := by
  rw [hq0]
  ring
theorem c6_cheap_prefix_state_formula_last
    (n k qLast : Nat) (hqLast : qLast = 1 + 2 ^ 2 * 3 ^ (n - 1) * k) :
    qLast = 1 + 4 * 3 ^ (n - 1) * k := by
  rw [hqLast]
  norm_num
theorem c6_cheap_chain_forward_lift_to_three_q
    (n q0 q1 : Nat)
    (hq1 : q1 = (3 * q0 + 1) / 4)
    (hdiv : 4 ∣ 3 * q0 + 1)
    (hres : Nat.ModEq (2 ^ (2 * n)) q1 1) :
    Nat.ModEq (2 ^ (2 * n + 2)) (3 * q0) 3 := by
  obtain ⟨s, hs⟩ := hdiv
  have hq1s : q1 = s := by
    rw [hq1, hs]
    exact Nat.mul_div_right s (by norm_num : 0 < 4)
  rw [hq1s] at hres
  have hmul : Nat.ModEq (2 ^ (2 * n) * 4) (s * 4) (1 * 4) := by
    have hraw : Nat.ModEq (4 * 2 ^ (2 * n)) (4 * s) (4 * 1) :=
      Nat.ModEq.mul_left' 4 hres
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hraw
  have hmodulus : 2 ^ (2 * n + 2) = 2 ^ (2 * n) * 4 := by
    rw [pow_add]
    norm_num
  rw [← hmodulus] at hmul
  have hsq : s * 4 = 3 * q0 + 1 := by omega
  rw [hsq] at hmul
  have hcancel : Nat.ModEq (2 ^ (2 * n + 2)) (3 * q0) 3 :=
    Nat.ModEq.add_right_cancel' 1 (by simpa using hmul)
  exact hcancel
theorem c6_pow_two_coprime_three (e : Nat) :
    Nat.gcd (2 ^ e) 3 = 1 := by
  have hcop : Nat.Coprime (2 ^ e) 3 :=
    Nat.Coprime.pow_left e ((by native_decide) : Nat.Coprime 2 3)
  exact hcop.gcd_eq_one
theorem c6_cheap_chain_cancel_three
    (n q0 : Nat)
    (hthree : Nat.ModEq (2 ^ (2 * n + 2)) (3 * q0) 3) :
    Nat.ModEq (2 ^ (2 * n + 2)) q0 1 := by
  have hshape : Nat.ModEq (2 ^ (2 * n + 2)) (3 * q0) (3 * 1) := by
    simpa using hthree
  exact Nat.ModEq.cancel_left_of_coprime
    (c6_pow_two_coprime_three (2 * n + 2)) hshape
theorem c6_cheap_chain_forward_parent_residue
    (n q0 q1 : Nat)
    (hq1 : q1 = (3 * q0 + 1) / 4)
    (hdiv : 4 ∣ 3 * q0 + 1)
    (hres : Nat.ModEq (2 ^ (2 * n)) q1 1) :
    Nat.ModEq (2 ^ (2 * n + 2)) q0 1 :=
  c6_cheap_chain_cancel_three n q0
    (c6_cheap_chain_forward_lift_to_three_q n q0 q1 hq1 hdiv hres)
theorem c6_cheap_chain_reverse_child_formula
    (n k q0 q1 : Nat)
    (hq0 : q0 = 1 + 2 ^ (2 * n + 2) * k)
    (hq1 : q1 = 1 + 3 * 2 ^ (2 * n) * k) :
    q1 = (3 * q0 + 1) / 4 := by
  subst q0
  subst q1
  have hpow : 2 ^ (2 * n + 2) = 2 ^ (2 * n) * 4 := by
    rw [pow_add]
    norm_num
  rw [hpow]
  have hnum :
      3 * (1 + (2 ^ (2 * n) * 4) * k) + 1 =
        4 * (1 + 3 * 2 ^ (2 * n) * k) := by
    ring
  rw [hnum]
  have hdiv :
      4 * (1 + 3 * 2 ^ (2 * n) * k) / 4 =
        1 + 3 * 2 ^ (2 * n) * k :=
    Nat.mul_div_right (1 + 3 * 2 ^ (2 * n) * k) (by norm_num : 0 < 4)
  rw [hdiv]
theorem c6_cheap_chain_reverse_child_residue
    (n k q1 : Nat) (hq1 : q1 = 1 + 3 * 2 ^ (2 * n) * k) :
    Nat.ModEq (2 ^ (2 * n)) q1 1 := by
  rw [hq1]
  have hmul : 3 * 2 ^ (2 * n) * k = 2 ^ (2 * n) * (3 * k) := by ring
  rw [hmul]
  have hzero : Nat.ModEq (2 ^ (2 * n)) (2 ^ (2 * n) * (3 * k)) 0 :=
    Nat.ModEq.symm (Nat.modEq_iff_dvd.mpr (by use 3 * k; rfl))
  have hadd := Nat.ModEq.add_left 1 hzero
  simpa only [Nat.add_zero] using hadd
def c6CheapOneStage (q q' : Nat) : Prop :=
  q' = (3 * q + 1) / 4 ∧
  4 ∣ 3 * q + 1 ∧
  Nat.ModEq 8 q 1
def c6BeginsCheapChainLength : Nat → Nat → Prop
  | 0, _ => False
  | 1, q => q % 2 = 1 ∧ Nat.ModEq 4 q 1
  | n + 2, q0 =>
      ∃ q1, c6CheapOneStage q0 q1 ∧ c6BeginsCheapChainLength (n + 1) q1
theorem c6_exists_add_one_pow_two_mul_of_modEq
    (e q : Nat) (he : 1 ≤ e) (hres : Nat.ModEq (2 ^ e) q 1) :
    ∃ k, q = 1 + 2 ^ e * k := by
  have hq1 : 1 ≤ q := by
    by_contra h
    have hq0 : q = 0 := by omega
    subst hq0
    unfold Nat.ModEq at hres
    have h2 : 2 ≤ 2 ^ e := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    have h0 : (0 : Nat) % 2 ^ e = 0 := Nat.zero_mod _
    have h1 : (1 : Nat) % 2 ^ e = 1 := Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by decide) h2)
    rw [h0, h1] at hres
    omega
  have hdvd : 2 ^ e ∣ q - 1 := (Nat.modEq_iff_dvd' hq1).mp (Nat.ModEq.symm hres)
  obtain ⟨k, hk⟩ := hdvd
  use k
  omega
theorem c6_cheap_chain_congruence_base
    (q : Nat) :
    c6BeginsCheapChainLength 1 q ↔ Nat.ModEq (2 ^ (2 * 1)) q 1 := by
  constructor
  · rintro ⟨hodd, hres4⟩
    have hpow : 2 ^ (2 * 1) = 4 := by norm_num
    rw [hpow]
    exact hres4
  · intro hres
    have hpow : 2 ^ (2 * 1) = 4 := by norm_num
    rw [hpow] at hres
    refine ⟨?_, hres⟩
    unfold Nat.ModEq at hres
    omega
theorem c6_cheap_chain_reverse_parent_to_child
    (n q0 : Nat) (hn : 1 ≤ n)
    (hres : Nat.ModEq (2 ^ (2 * n + 2)) q0 1) :
    ∃ k q1,
      q0 = 1 + 2 ^ (2 * n + 2) * k ∧
      q1 = 1 + 3 * 2 ^ (2 * n) * k ∧
      c6CheapOneStage q0 q1 ∧
      Nat.ModEq (2 ^ (2 * n)) q1 1 := by
  obtain ⟨k, hk⟩ :=
    c6_exists_add_one_pow_two_mul_of_modEq (2 * n + 2) q0 (by omega : 1 ≤ 2 * n + 2) hres
  set q1 := 1 + 3 * 2 ^ (2 * n) * k
  have hq1 : q1 = 1 + 3 * 2 ^ (2 * n) * k := rfl
  have hmod8 : Nat.ModEq 8 q0 1 := by
    have h8 : 8 ∣ 2 ^ (2 * n + 2) := by
      rw [show 8 = 2 ^ 3 by norm_num]
      refine pow_dvd_pow _ (Nat.le_trans (by decide : 3 ≤ 4) ?_)
      omega
    exact Nat.ModEq.of_dvd h8 hres
  have hnum :
      3 * (1 + 2 ^ (2 * n + 2) * k) + 1 = 4 * q1 := by
    dsimp [q1]
    have hpow : 2 ^ (2 * n + 2) = 2 ^ (2 * n) * 4 := by
      rw [pow_add]
      norm_num
    rw [hpow]
    ring
  have hstage : c6CheapOneStage q0 q1 :=
    ⟨c6_cheap_chain_reverse_child_formula n k q0 q1 hk hq1,
      by rw [hk, hnum]; exact Nat.dvd_mul_right 4 q1,
      hmod8⟩
  exact ⟨k, q1, hk, hq1, hstage, c6_cheap_chain_reverse_child_residue n k q1 hq1⟩
theorem c6_cheap_chain_congruence_criterion
    (n q : Nat) (hn : 1 ≤ n) :
    c6BeginsCheapChainLength n q ↔ Nat.ModEq (2 ^ (2 * n)) q 1 := by
  match n with
  | 0 => omega
  | 1 => exact c6_cheap_chain_congruence_base q
  | n + 2 =>
    constructor
    · intro hchain
      rcases hchain with ⟨q1, hstage, htail⟩
      have ih :
          c6BeginsCheapChainLength (n + 1) q1 ↔
            Nat.ModEq (2 ^ (2 * (n + 1))) q1 1 :=
        c6_cheap_chain_congruence_criterion (n + 1) q1 (by omega)
      have hres1 : Nat.ModEq (2 ^ (2 * (n + 1))) q1 1 := ih.mp htail
      rcases hstage with ⟨hq1, hdiv, _⟩
      exact c6_cheap_chain_forward_parent_residue (n + 1) q q1 hq1 hdiv hres1
    · intro hres
      rcases c6_cheap_chain_reverse_parent_to_child (n + 1) q (by omega) hres with
        ⟨k, q1, hk, hq1, hstage, hres1⟩
      refine ⟨q1, hstage, ?_⟩
      have ih :
          c6BeginsCheapChainLength (n + 1) q1 ↔
            Nat.ModEq (2 ^ (2 * (n + 1))) q1 1 :=
        c6_cheap_chain_congruence_criterion (n + 1) q1 (by omega)
      exact ih.mpr hres1
theorem c6_cheap_chain_length_bound
    (n q : Nat) (hn : 1 ≤ n) (hqpos : 1 < q)
    (hres : Nat.ModEq (2 ^ (2 * n)) q 1) :
    2 ^ (2 * n) ≤ q - 1 := by
  obtain ⟨k, hk⟩ :=
    c6_exists_add_one_pow_two_mul_of_modEq (2 * n) q (by omega : 1 ≤ 2 * n) hres
  have hkpos : 1 ≤ k := by
    rw [hk] at hqpos
    by_contra h
    have hk0 : k = 0 := by omega
    subst hk0
    rw [Nat.mul_zero, Nat.add_zero] at hk hqpos
    omega
  calc
    2 ^ (2 * n) = 2 ^ (2 * n) * 1 := by simp
    _ ≤ 2 ^ (2 * n) * k := Nat.mul_le_mul_left _ hkpos
    _ = q - 1 := by omega
theorem c6_cheap_prefix_Ln1_residue_of_even_k
    (n q0 k t : Nat) (hq0 : q0 = 1 + 2 ^ (2 * n) * k)
    (hk : k = 2 * t) :
    Nat.ModEq (2 ^ (2 * n + 1)) q0 1 := by
  subst q0
  subst k
  have hmul :
      2 ^ (2 * n) * (2 * t) = 2 ^ (2 * n + 1) * t := by
    rw [pow_succ]
    ring
  rw [hmul]
  exact Nat.ModEq.symm (Nat.modEq_iff_dvd.mpr (by use t; omega))
theorem c6_cheap_prefix_even_k_of_Ln1_residue
    (n q0 k : Nat) (hq0 : q0 = 1 + 2 ^ (2 * n) * k)
    (hres : Nat.ModEq (2 ^ (2 * n + 1)) q0 1) :
    k % 2 = 0 := by
  subst q0
  have hcancel :
      Nat.ModEq (2 ^ (2 * n + 1)) (2 ^ (2 * n) * k) 0 :=
    Nat.ModEq.add_left_cancel' 1 (by simpa using hres)
  have hrewrite :
      Nat.ModEq (2 ^ (2 * n) * 2)
        (2 ^ (2 * n) * k) (2 ^ (2 * n) * 0) := by
    simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcancel
  have hk2 : Nat.ModEq 2 k 0 :=
    Nat.ModEq.mul_left_cancel'
      (pow_ne_zero (2 * n) (by norm_num : (2 : Nat) ≠ 0)) hrewrite
  unfold Nat.ModEq at hk2
  simpa using hk2
theorem c6_cheap_prefix_Ln2_residue_of_k_mod4
    (n q0 k : Nat) (hq0 : q0 = 1 + 2 ^ (2 * n) * k)
    (hk : Nat.ModEq 4 k (3 ^ n)) :
    Nat.ModEq (2 ^ (2 * n + 2)) q0 (1 + 3 ^ n * 2 ^ (2 * n)) := by
  subst q0
  have hmul :
      Nat.ModEq (2 ^ (2 * n + 2))
        (2 ^ (2 * n) * k) (2 ^ (2 * n) * 3 ^ n) := by
    have hraw :
        Nat.ModEq (2 ^ (2 * n) * 4)
          (2 ^ (2 * n) * k) (2 ^ (2 * n) * 3 ^ n) :=
      Nat.ModEq.mul_left' (2 ^ (2 * n)) hk
    simpa [pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hraw
  have hadd := Nat.ModEq.add_left 1 hmul
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hadd
theorem c6_cheap_prefix_k_mod4_of_Ln2_residue
    (n q0 k : Nat) (hq0 : q0 = 1 + 2 ^ (2 * n) * k)
    (hres : Nat.ModEq (2 ^ (2 * n + 2)) q0 (1 + 3 ^ n * 2 ^ (2 * n))) :
    Nat.ModEq 4 k (3 ^ n) := by
  subst q0
  have hcanon :
      Nat.ModEq (2 ^ (2 * n + 2))
        (1 + 2 ^ (2 * n) * k) (1 + 2 ^ (2 * n) * 3 ^ n) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hres
  have hcancel :
      Nat.ModEq (2 ^ (2 * n + 2))
        (2 ^ (2 * n) * k) (2 ^ (2 * n) * 3 ^ n) :=
    Nat.ModEq.add_left_cancel' 1 hcanon
  have hrewrite :
      Nat.ModEq (2 ^ (2 * n) * 4)
        (2 ^ (2 * n) * k) (2 ^ (2 * n) * 3 ^ n) := by
    simpa [pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcancel
  exact Nat.ModEq.mul_left_cancel'
    (pow_ne_zero (2 * n) (by norm_num : (2 : Nat) ≠ 0)) hrewrite
theorem c6_cheap_prefix_Ln_ge3_residue_of_k_mod4
    (n q0 k : Nat) (hq0 : q0 = 1 + 2 ^ (2 * n) * k)
    (hk : Nat.ModEq 4 k (3 ^ (n - 1))) :
    Nat.ModEq (2 ^ (2 * n + 2)) q0 (1 + 3 ^ (n - 1) * 2 ^ (2 * n)) := by
  subst q0
  have hmul :
      Nat.ModEq (2 ^ (2 * n + 2))
        (2 ^ (2 * n) * k) (2 ^ (2 * n) * 3 ^ (n - 1)) := by
    have hraw :
        Nat.ModEq (2 ^ (2 * n) * 4)
          (2 ^ (2 * n) * k) (2 ^ (2 * n) * 3 ^ (n - 1)) :=
      Nat.ModEq.mul_left' (2 ^ (2 * n)) hk
    simpa [pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hraw
  have hadd := Nat.ModEq.add_left 1 hmul
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hadd
theorem c6_cheap_prefix_k_mod4_of_Ln_ge3_residue
    (n q0 k : Nat) (hq0 : q0 = 1 + 2 ^ (2 * n) * k)
    (hres : Nat.ModEq (2 ^ (2 * n + 2)) q0
      (1 + 3 ^ (n - 1) * 2 ^ (2 * n))) :
    Nat.ModEq 4 k (3 ^ (n - 1)) := by
  subst q0
  have hcanon :
      Nat.ModEq (2 ^ (2 * n + 2))
        (1 + 2 ^ (2 * n) * k) (1 + 2 ^ (2 * n) * 3 ^ (n - 1)) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hres
  have hcancel :
      Nat.ModEq (2 ^ (2 * n + 2))
        (2 ^ (2 * n) * k) (2 ^ (2 * n) * 3 ^ (n - 1)) :=
    Nat.ModEq.add_left_cancel' 1 hcanon
  have hrewrite :
      Nat.ModEq (2 ^ (2 * n) * 4)
        (2 ^ (2 * n) * k) (2 ^ (2 * n) * 3 ^ (n - 1)) := by
    simpa [pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcancel
  exact Nat.ModEq.mul_left_cancel'
    (pow_ne_zero (2 * n) (by norm_num : (2 : Nat) ≠ 0)) hrewrite
theorem c6_cheap_prefix_k_exists
    (n q0 : Nat) (hn : 1 ≤ n) (hchain : c6BeginsCheapChainLength n q0) :
    ∃ k, q0 = 1 + 2 ^ (2 * n) * k := by
  obtain ⟨k, hk⟩ :=
    c6_exists_add_one_pow_two_mul_of_modEq (2 * n) q0 (by omega : 1 ≤ 2 * n)
      ((c6_cheap_chain_congruence_criterion n q0 hn).mp hchain)
  exact ⟨k, hk⟩
theorem c6_cheap_prefix_first_deviation_Ln1_iff
    (n q0 : Nat) (hn : 1 ≤ n) (hchain : c6BeginsCheapChainLength n q0) :
    Nat.ModEq (2 ^ (2 * n + 1)) q0 1 ↔
      ∃ k t, q0 = 1 + 2 ^ (2 * n) * k ∧ k = 2 * t := by
  constructor
  · intro hres
    obtain ⟨k, hk⟩ := c6_cheap_prefix_k_exists n q0 hn hchain
    have heven := c6_cheap_prefix_even_k_of_Ln1_residue n q0 k hk hres
    have htwo : 2 ∣ k := Nat.dvd_of_mod_eq_zero heven
    obtain ⟨t, ht⟩ := htwo
    exact ⟨k, t, hk, ht⟩
  · intro ⟨k, t, hk, ht⟩
    exact c6_cheap_prefix_Ln1_residue_of_even_k n q0 k t hk ht
theorem c6_cheap_prefix_first_deviation_Ln2_iff
    (n q0 : Nat) (hn : 1 ≤ n) (hchain : c6BeginsCheapChainLength n q0) :
    Nat.ModEq (2 ^ (2 * n + 2)) q0 (1 + 3 ^ n * 2 ^ (2 * n)) ↔
      ∃ k, q0 = 1 + 2 ^ (2 * n) * k ∧ Nat.ModEq 4 k (3 ^ n) := by
  constructor
  · intro hres
    obtain ⟨k, hk⟩ := c6_cheap_prefix_k_exists n q0 hn hchain
    exact ⟨k, hk, c6_cheap_prefix_k_mod4_of_Ln2_residue n q0 k hk hres⟩
  · intro ⟨k, hk, hmod⟩
    exact c6_cheap_prefix_Ln2_residue_of_k_mod4 n q0 k hk hmod
theorem c6_cheap_prefix_first_deviation_LnGe3_iff
    (n q0 : Nat) (hn : 1 ≤ n) (hchain : c6BeginsCheapChainLength n q0) :
    Nat.ModEq (2 ^ (2 * n + 2)) q0 (1 + 3 ^ (n - 1) * 2 ^ (2 * n)) ↔
      ∃ k, q0 = 1 + 2 ^ (2 * n) * k ∧ Nat.ModEq 4 k (3 ^ (n - 1)) := by
  constructor
  · intro hres
    obtain ⟨k, hk⟩ := c6_cheap_prefix_k_exists n q0 hn hchain
    exact ⟨k, hk, c6_cheap_prefix_k_mod4_of_Ln_ge3_residue n q0 k hk hres⟩
  · intro ⟨k, hk, hmod⟩
    exact c6_cheap_prefix_Ln_ge3_residue_of_k_mod4 n q0 k hk hmod
structure C6ShiftedL1NormalForm (n q0 : Nat) where
  t : Nat
  q0_eq : q0 = 1 + 2 ^ (2 * n + 1) * t
  qLast : Nat
  qLast_eq : qLast = 1 + 8 * 3 ^ (n - 1) * t
  qn : Nat
  qn_eq : qn = 1 + 2 * 3 ^ n * t
theorem c6_shifted_Ln1_qn_formula
    (n qLast qn t : Nat) (hn : 1 <= n)
    (hqLast : qLast = 1 + 8 * 3 ^ (n - 1) * t)
    (hqn : qn = 1 + 2 * 3 ^ n * t) :
    qn = (3 * qLast + 1) / 4 := by
  subst qLast
  subst qn
  have hpow : 3 ^ n = 3 ^ (n - 1) * 3 := by
    calc
      3 ^ n = 3 ^ ((n - 1) + 1) := by
        exact congrArg (fun m => 3 ^ m) (by omega : n = (n - 1) + 1)
      _ = 3 ^ (n - 1) * 3 := by
        rw [pow_succ]
  rw [hpow]
  have hnum :
      3 * (1 + 8 * 3 ^ (n - 1) * t) + 1 =
        4 * (1 + 2 * (3 ^ (n - 1) * 3) * t) := by
    ring
  rw [hnum]
  have hdiv :
      4 * (1 + 2 * (3 ^ (n - 1) * 3) * t) / 4 =
        1 + 2 * (3 ^ (n - 1) * 3) * t :=
    Nat.mul_div_right (1 + 2 * (3 ^ (n - 1) * 3) * t) (by norm_num : 0 < 4)
  rw [hdiv]
theorem c6_shifted_Ln1_resonance1_residue_of_even_t
    (n q0 t k : Nat) (hq0 : q0 = 1 + 2 ^ (2 * n + 1) * t)
    (ht : t = 2 * k) :
    Nat.ModEq (2 ^ (2 * n + 2)) q0 1 := by
  subst q0
  subst t
  have hmul :
      2 ^ (2 * n + 1) * (2 * k) = 2 ^ (2 * n + 2) * k := by
    rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, pow_succ]
    ring
  rw [hmul]
  exact Nat.ModEq.symm (Nat.modEq_iff_dvd.mpr (by use k; omega))
theorem c6_shifted_Ln1_even_t_of_resonance1_residue
    (n q0 t : Nat) (hq0 : q0 = 1 + 2 ^ (2 * n + 1) * t)
    (hres : Nat.ModEq (2 ^ (2 * n + 2)) q0 1) :
    t % 2 = 0 := by
  subst q0
  have hcancel :
      Nat.ModEq (2 ^ (2 * n + 2)) (2 ^ (2 * n + 1) * t) 0 :=
    Nat.ModEq.add_left_cancel' 1 (by simpa using hres)
  have hrewrite :
      Nat.ModEq (2 ^ (2 * n + 1) * 2)
        (2 ^ (2 * n + 1) * t) (2 ^ (2 * n + 1) * 0) := by
    simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      show 2 * n + 2 = (2 * n + 1) + 1 by omega] using hcancel
  have ht2 : Nat.ModEq 2 t 0 :=
    Nat.ModEq.mul_left_cancel'
      (pow_ne_zero (2 * n + 1) (by norm_num : (2 : Nat) ≠ 0)) hrewrite
  unfold Nat.ModEq at ht2
  simpa using ht2
theorem c6_shifted_Ln1_resonance_ge2_residue_of_odd_t
    (n q0 t : Nat) (hq0 : q0 = 1 + 2 ^ (2 * n + 1) * t)
    (ht : Nat.ModEq 2 t 1) :
    Nat.ModEq (2 ^ (2 * n + 2)) q0 (1 + 2 ^ (2 * n + 1)) := by
  subst q0
  have hmul :
      Nat.ModEq (2 ^ (2 * n + 2))
        (2 ^ (2 * n + 1) * t) (2 ^ (2 * n + 1) * 1) := by
    have hraw :
        Nat.ModEq (2 ^ (2 * n + 1) * 2)
          (2 ^ (2 * n + 1) * t) (2 ^ (2 * n + 1) * 1) :=
      Nat.ModEq.mul_left' (2 ^ (2 * n + 1)) ht
    simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      show 2 * n + 2 = (2 * n + 1) + 1 by omega] using hraw
  have hadd := Nat.ModEq.add_left 1 hmul
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hadd
theorem c6_shifted_Ln1_odd_t_of_resonance_ge2_residue
    (n q0 t : Nat) (hq0 : q0 = 1 + 2 ^ (2 * n + 1) * t)
    (hres : Nat.ModEq (2 ^ (2 * n + 2)) q0 (1 + 2 ^ (2 * n + 1))) :
    Nat.ModEq 2 t 1 := by
  subst q0
  have hcanon :
      Nat.ModEq (2 ^ (2 * n + 2))
        (1 + 2 ^ (2 * n + 1) * t) (1 + 2 ^ (2 * n + 1) * 1) := by
    simpa using hres
  have hcancel :
      Nat.ModEq (2 ^ (2 * n + 2))
        (2 ^ (2 * n + 1) * t) (2 ^ (2 * n + 1) * 1) :=
    Nat.ModEq.add_left_cancel' 1 hcanon
  have hrewrite :
      Nat.ModEq (2 ^ (2 * n + 1) * 2)
        (2 ^ (2 * n + 1) * t) (2 ^ (2 * n + 1) * 1) := by
    simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      show 2 * n + 2 = (2 * n + 1) + 1 by omega] using hcancel
  exact Nat.ModEq.mul_left_cancel'
    (pow_ne_zero (2 * n + 1) (by norm_num : (2 : Nat) ≠ 0)) hrewrite
theorem c6_shifted_Ln1_next_length1_residue_of_even_v
    (n q0 v k : Nat) (hq0 : q0 = 1 + 2 ^ (2 * n + 2) * v)
    (hv : v = 2 * k) :
    Nat.ModEq (2 ^ (2 * n + 3)) q0 1 := by
  subst q0
  subst v
  have hmul :
      2 ^ (2 * n + 2) * (2 * k) = 2 ^ (2 * n + 3) * k := by
    rw [show 2 * n + 3 = (2 * n + 2) + 1 by omega, pow_succ]
    ring
  rw [hmul]
  exact Nat.ModEq.symm (Nat.modEq_iff_dvd.mpr (by use k; omega))
theorem c6_shifted_Ln1_even_v_of_next_length1_residue
    (n q0 v : Nat) (hq0 : q0 = 1 + 2 ^ (2 * n + 2) * v)
    (hres : Nat.ModEq (2 ^ (2 * n + 3)) q0 1) :
    v % 2 = 0 := by
  subst q0
  have hcancel :
      Nat.ModEq (2 ^ (2 * n + 3)) (2 ^ (2 * n + 2) * v) 0 :=
    Nat.ModEq.add_left_cancel' 1 (by simpa using hres)
  have hrewrite :
      Nat.ModEq (2 ^ (2 * n + 2) * 2)
        (2 ^ (2 * n + 2) * v) (2 ^ (2 * n + 2) * 0) := by
    simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      show 2 * n + 3 = (2 * n + 2) + 1 by omega] using hcancel
  have hv2 : Nat.ModEq 2 v 0 :=
    Nat.ModEq.mul_left_cancel'
      (pow_ne_zero (2 * n + 2) (by norm_num : (2 : Nat) ≠ 0)) hrewrite
  unfold Nat.ModEq at hv2
  simpa using hv2
theorem c6_shifted_Ln1_next_length2_residue_of_v_mod4
    (n q0 v : Nat) (hq0 : q0 = 1 + 2 ^ (2 * n + 2) * v)
    (hv : Nat.ModEq 4 v (3 ^ (n + 1))) :
    Nat.ModEq (2 ^ (2 * n + 4)) q0
      (1 + 3 ^ (n + 1) * 2 ^ (2 * n + 2)) := by
  subst q0
  have hmul :
      Nat.ModEq (2 ^ (2 * n + 4))
        (2 ^ (2 * n + 2) * v)
        (2 ^ (2 * n + 2) * 3 ^ (n + 1)) := by
    have hraw :
        Nat.ModEq (2 ^ (2 * n + 2) * 4)
          (2 ^ (2 * n + 2) * v)
          (2 ^ (2 * n + 2) * 3 ^ (n + 1)) :=
      Nat.ModEq.mul_left' (2 ^ (2 * n + 2)) hv
    simpa [pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hraw
  have hadd := Nat.ModEq.add_left 1 hmul
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hadd
theorem c6_shifted_Ln1_v_mod4_of_next_length2_residue
    (n q0 v : Nat) (hq0 : q0 = 1 + 2 ^ (2 * n + 2) * v)
    (hres : Nat.ModEq (2 ^ (2 * n + 4)) q0
      (1 + 3 ^ (n + 1) * 2 ^ (2 * n + 2))) :
    Nat.ModEq 4 v (3 ^ (n + 1)) := by
  subst q0
  have hcanon :
      Nat.ModEq (2 ^ (2 * n + 4))
        (1 + 2 ^ (2 * n + 2) * v)
        (1 + 2 ^ (2 * n + 2) * 3 ^ (n + 1)) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hres
  have hcancel :
      Nat.ModEq (2 ^ (2 * n + 4))
        (2 ^ (2 * n + 2) * v)
        (2 ^ (2 * n + 2) * 3 ^ (n + 1)) :=
    Nat.ModEq.add_left_cancel' 1 hcanon
  have hrewrite :
      Nat.ModEq (2 ^ (2 * n + 2) * 4)
        (2 ^ (2 * n + 2) * v)
        (2 ^ (2 * n + 2) * 3 ^ (n + 1)) := by
    simpa [pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcancel
  exact Nat.ModEq.mul_left_cancel'
    (pow_ne_zero (2 * n + 2) (by norm_num : (2 : Nat) ≠ 0)) hrewrite
theorem c6_shifted_Ln1_next_length_ge3_residue_of_v_mod4
    (n q0 v : Nat) (hq0 : q0 = 1 + 2 ^ (2 * n + 2) * v)
    (hv : Nat.ModEq 4 v (3 ^ n)) :
    Nat.ModEq (2 ^ (2 * n + 4)) q0
      (1 + 3 ^ n * 2 ^ (2 * n + 2)) := by
  subst q0
  have hmul :
      Nat.ModEq (2 ^ (2 * n + 4))
        (2 ^ (2 * n + 2) * v)
        (2 ^ (2 * n + 2) * 3 ^ n) := by
    have hraw :
        Nat.ModEq (2 ^ (2 * n + 2) * 4)
          (2 ^ (2 * n + 2) * v)
          (2 ^ (2 * n + 2) * 3 ^ n) :=
      Nat.ModEq.mul_left' (2 ^ (2 * n + 2)) hv
    simpa [pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hraw
  have hadd := Nat.ModEq.add_left 1 hmul
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hadd
theorem c6_shifted_Ln1_v_mod4_of_next_length_ge3_residue
    (n q0 v : Nat) (hq0 : q0 = 1 + 2 ^ (2 * n + 2) * v)
    (hres : Nat.ModEq (2 ^ (2 * n + 4)) q0
      (1 + 3 ^ n * 2 ^ (2 * n + 2))) :
    Nat.ModEq 4 v (3 ^ n) := by
  subst q0
  have hcanon :
      Nat.ModEq (2 ^ (2 * n + 4))
        (1 + 2 ^ (2 * n + 2) * v)
        (1 + 2 ^ (2 * n + 2) * 3 ^ n) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hres
  have hcancel :
      Nat.ModEq (2 ^ (2 * n + 4))
        (2 ^ (2 * n + 2) * v)
        (2 ^ (2 * n + 2) * 3 ^ n) :=
    Nat.ModEq.add_left_cancel' 1 hcanon
  have hrewrite :
      Nat.ModEq (2 ^ (2 * n + 2) * 4)
        (2 ^ (2 * n + 2) * v)
        (2 ^ (2 * n + 2) * 3 ^ n) := by
    simpa [pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcancel
  exact Nat.ModEq.mul_left_cancel'
    (pow_ne_zero (2 * n + 2) (by norm_num : (2 : Nat) ≠ 0)) hrewrite
structure C6ShiftedL2NormalForm (n q0 : Nat) where
  t : Nat
  q0_eq : q0 = 1 + 2 ^ (2 * n) * (3 ^ n + 4 * t)
theorem c6_shifted_Ln2_base_residue
    (n q0 : Nat) (N : C6ShiftedL2NormalForm n q0) :
    Nat.ModEq (2 ^ (2 * n + 2)) q0 (1 + 3 ^ n * 2 ^ (2 * n)) := by
  rw [N.q0_eq]
  have hmul :
      Nat.ModEq (2 ^ (2 * n + 2))
        (2 ^ (2 * n) * (3 ^ n + 4 * N.t))
        (2 ^ (2 * n) * 3 ^ n) := by
    have hdiff :
        2 ^ (2 * n) * (3 ^ n + 4 * N.t) =
          2 ^ (2 * n) * 3 ^ n + (2 ^ (2 * n) * 4) * N.t := by
      ring
    rw [hdiff]
    exact Nat.ModEq.symm (Nat.modEq_iff_dvd.mpr (by
      use N.t
      rw [show 2 ^ (2 * n + 2) = 2 ^ (2 * n) * 4 by
        rw [show 2 * n + 2 = 2 * n + 2 by rfl, pow_add]
        norm_num]
      omega))
  have hadd := Nat.ModEq.add_left 1 hmul
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hadd
theorem c6_shifted_Ln2_resonance1_residue_of_even_t
    (n q0 t k : Nat)
    (hq0 : q0 = 1 + 2 ^ (2 * n) * (3 ^ n + 4 * t))
    (ht : t = 2 * k) :
    Nat.ModEq (2 ^ (2 * n + 3)) q0 (1 + 3 ^ n * 2 ^ (2 * n)) := by
  subst q0
  subst t
  have hmul :
      Nat.ModEq (2 ^ (2 * n + 3))
        (2 ^ (2 * n) * (3 ^ n + 4 * (2 * k)))
        (2 ^ (2 * n) * 3 ^ n) := by
    have hdiff :
        2 ^ (2 * n) * (3 ^ n + 4 * (2 * k)) =
          2 ^ (2 * n) * 3 ^ n + (2 ^ (2 * n) * 8) * k := by
      ring
    rw [hdiff]
    exact Nat.ModEq.symm (Nat.modEq_iff_dvd.mpr (by
      use k
      rw [show 2 ^ (2 * n + 3) = 2 ^ (2 * n) * 8 by
        rw [show 2 * n + 3 = 2 * n + 3 by rfl, pow_add]
        norm_num]
      omega))
  have hadd := Nat.ModEq.add_left 1 hmul
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hadd
theorem c6_shifted_Ln2_even_t_of_resonance1_residue
    (n q0 t : Nat)
    (hq0 : q0 = 1 + 2 ^ (2 * n) * (3 ^ n + 4 * t))
    (hres : Nat.ModEq (2 ^ (2 * n + 3)) q0 (1 + 3 ^ n * 2 ^ (2 * n))) :
    t % 2 = 0 := by
  subst q0
  have hcanon :
      Nat.ModEq (2 ^ (2 * n + 3))
        (1 + 2 ^ (2 * n) * (3 ^ n + 4 * t))
        (1 + 2 ^ (2 * n) * 3 ^ n) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hres
  have hcancel :
      Nat.ModEq (2 ^ (2 * n + 3))
        (2 ^ (2 * n) * (3 ^ n + 4 * t)) (2 ^ (2 * n) * 3 ^ n) :=
    Nat.ModEq.add_left_cancel' 1 hcanon
  have hrewrite :
      Nat.ModEq (2 ^ (2 * n) * 8)
        (2 ^ (2 * n) * 3 ^ n + (2 ^ (2 * n) * 4) * t)
        (2 ^ (2 * n) * 3 ^ n + (2 ^ (2 * n) * 4) * 0) := by
    have hleft :
        2 ^ (2 * n) * (3 ^ n + 4 * t) =
          2 ^ (2 * n) * 3 ^ n + (2 ^ (2 * n) * 4) * t := by ring
    rw [← hleft]
    simpa [pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcancel
  have hremove :
      Nat.ModEq (2 ^ (2 * n) * 8)
        ((2 ^ (2 * n) * 4) * t) ((2 ^ (2 * n) * 4) * 0) :=
    Nat.ModEq.add_left_cancel' (2 ^ (2 * n) * 3 ^ n) hrewrite
  have hmod2 : Nat.ModEq 2 t 0 := by
    have hfactor :
        Nat.ModEq ((2 ^ (2 * n) * 4) * 2)
          ((2 ^ (2 * n) * 4) * t) ((2 ^ (2 * n) * 4) * 0) := by
      have hmodulus : (2 ^ (2 * n) * 4) * 2 = 2 ^ (2 * n) * 8 := by ring
      rw [hmodulus]
      exact hremove
    exact Nat.ModEq.mul_left_cancel'
      (by
        exact mul_ne_zero
          (pow_ne_zero (2 * n) (by norm_num : (2 : Nat) ≠ 0))
          (by norm_num : 4 ≠ 0)) hfactor
  unfold Nat.ModEq at hmod2
  simpa using hmod2
theorem c6_shifted_Ln2_resonance_ge2_residue_of_odd_t
    (n q0 t : Nat)
    (hq0 : q0 = 1 + 2 ^ (2 * n) * (3 ^ n + 4 * t))
    (ht : Nat.ModEq 2 t 1) :
    Nat.ModEq (2 ^ (2 * n + 3)) q0
      (1 + 3 ^ n * 2 ^ (2 * n) + 2 ^ (2 * n + 2)) := by
  subst q0
  have hmul :
      Nat.ModEq (2 ^ (2 * n + 3))
        (2 ^ (2 * n) * (3 ^ n + 4 * t))
        (2 ^ (2 * n) * 3 ^ n + 2 ^ (2 * n + 2)) := by
    have hraw :
        Nat.ModEq ((2 ^ (2 * n) * 4) * 2)
          ((2 ^ (2 * n) * 4) * t) ((2 ^ (2 * n) * 4) * 1) :=
      Nat.ModEq.mul_left' (2 ^ (2 * n) * 4) ht
    have hbase :
        Nat.ModEq (2 ^ (2 * n + 3))
          ((2 ^ (2 * n) * 4) * t) ((2 ^ (2 * n) * 4) * 1) := by
      have hmodulus : 2 ^ (2 * n + 3) = (2 ^ (2 * n) * 4) * 2 := by
        rw [pow_add]
        norm_num
        ring
      rw [hmodulus]
      exact hraw
    have hadd := Nat.ModEq.add_left (2 ^ (2 * n) * 3 ^ n) hbase
    have hleft :
        2 ^ (2 * n) * (3 ^ n + 4 * t) =
          2 ^ (2 * n) * 3 ^ n + (2 ^ (2 * n) * 4) * t := by ring
    have hright :
        2 ^ (2 * n) * 3 ^ n + 2 ^ (2 * n + 2) =
          2 ^ (2 * n) * 3 ^ n + (2 ^ (2 * n) * 4) * 1 := by
      rw [pow_add]
      norm_num
    rw [hleft, hright]
    exact hadd
  have hadd := Nat.ModEq.add_left 1 hmul
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_add] using hadd
inductive C6OddMod8 where
  | one
  | three
  | five
  | seven
  deriving DecidableEq
def C6OddMod8.value : C6OddMod8 → Nat
  | .one => 1
  | .three => 3
  | .five => 5
  | .seven => 7
inductive C6LowValuedMod8State where
  | L1_q1
  | L1_q5
  | L2_q3
  | L2_q7
  deriving DecidableEq
def C6LowValuedMod8State.L : C6LowValuedMod8State → Nat
  | .L1_q1 => 1
  | .L1_q5 => 1
  | .L2_q3 => 2
  | .L2_q7 => 2
def C6LowValuedMod8State.qResidue : C6LowValuedMod8State → Nat
  | .L1_q1 => 1
  | .L1_q5 => 5
  | .L2_q3 => 3
  | .L2_q7 => 7
def c6_mod8_child_L1_q1 (t : Fin 4) : Nat :=
  (6 * (t : Nat) + 1) % 8
def c6_mod8_child_L1_q5 (t : Fin 4) : Nat :=
  (6 * (t : Nat) + 5) % 8
def c6_mod8_child_L2_q3 (t : Fin 4) : Nat :=
  (18 * (t : Nat) + 7) % 8
def c6_mod8_child_L2_q7 (t : Fin 4) : Nat :=
  (18 * (t : Nat) + 17) % 8
theorem c6_mod8_L1_q1_children :
    c6_mod8_child_L1_q1 0 = 1 ∧
    c6_mod8_child_L1_q1 1 = 7 ∧
    c6_mod8_child_L1_q1 2 = 5 ∧
    c6_mod8_child_L1_q1 3 = 3 := by
  decide
theorem c6_mod8_L1_q5_children :
    c6_mod8_child_L1_q5 0 = 5 ∧
    c6_mod8_child_L1_q5 1 = 3 ∧
    c6_mod8_child_L1_q5 2 = 1 ∧
    c6_mod8_child_L1_q5 3 = 7 := by
  decide
theorem c6_mod8_L2_q3_children :
    c6_mod8_child_L2_q3 0 = 7 ∧
    c6_mod8_child_L2_q3 1 = 1 ∧
    c6_mod8_child_L2_q3 2 = 3 ∧
    c6_mod8_child_L2_q3 3 = 5 := by
  decide
theorem c6_mod8_L2_q7_children :
    c6_mod8_child_L2_q7 0 = 1 ∧
    c6_mod8_child_L2_q7 1 = 3 ∧
    c6_mod8_child_L2_q7 2 = 5 ∧
    c6_mod8_child_L2_q7 3 = 7 := by
  decide
theorem c6_mod8_low_valued_surjective_children
    (state : C6LowValuedMod8State) (target : C6OddMod8) :
    ∃ t : Fin 4,
      match state with
      | .L1_q1 => c6_mod8_child_L1_q1 t = target.value
      | .L1_q5 => c6_mod8_child_L1_q5 t = target.value
      | .L2_q3 => c6_mod8_child_L2_q3 t = target.value
      | .L2_q7 => c6_mod8_child_L2_q7 t = target.value := by
  cases state <;> cases target
  all_goals
    first
    | exact ⟨0, by decide⟩
    | exact ⟨1, by decide⟩
    | exact ⟨2, by decide⟩
    | exact ⟨3, by decide⟩
noncomputable def c6DyadicMass (e : Nat) : Rat :=
  (1 : Rat) / (2 ^ e : Rat)
structure C6OddResidueClass where
  exponent : Nat
  residue : Nat
  residue_odd : residue % 2 = 1
def C6OddResidueClass.Contains (cls : C6OddResidueClass) (q : Nat) : Prop :=
  Nat.ModEq (2 ^ cls.exponent) q cls.residue
noncomputable def C6OddResidueClass.oddDensity (cls : C6OddResidueClass) : Rat :=
  c6DyadicMass (cls.exponent - 1)
theorem c6_odd_residue_class_nonempty (cls : C6OddResidueClass) :
    ∃ q, 0 < q ∧ q % 2 = 1 ∧ cls.Contains q := by
  refine ⟨cls.residue, ?_, cls.residue_odd, ?_⟩
  · have h : cls.residue % 2 ≠ 0 := by
      rw [cls.residue_odd]
      norm_num
    omega
  · unfold C6OddResidueClass.Contains
    exact Nat.ModEq.refl _
structure C6LowValuedWord where
  entries : List Nat
  entries_one_or_two : ∀ ell ∈ entries, ell = 1 ∨ ell = 2
namespace C6LowValuedWord
def length (lambda : C6LowValuedWord) : Nat :=
  lambda.entries.length
def weight (lambda : C6LowValuedWord) : Nat :=
  lambda.entries.sum
end C6LowValuedWord
structure C6LowValuedExactCylinder (lambda : C6LowValuedWord) where
  cls : C6OddResidueClass
  exponent_eq :
    cls.exponent = lambda.length + lambda.weight + 1
theorem c6_low_valued_exact_cylinder_density
    (lambda : C6LowValuedWord) (E : C6LowValuedExactCylinder lambda) :
    E.cls.oddDensity =
      c6DyadicMass (lambda.length + lambda.weight) := by
  unfold C6OddResidueClass.oddDensity
  rw [E.exponent_eq]
  rw [show lambda.length + lambda.weight + 1 - 1 =
    lambda.length + lambda.weight by omega]
theorem c6_low_valued_exact_cylinder_nonempty
    (lambda : C6LowValuedWord) (E : C6LowValuedExactCylinder lambda) :
    ∃ q, 0 < q ∧ q % 2 = 1 ∧ E.cls.Contains q :=
  c6_odd_residue_class_nonempty E.cls
theorem c6_low_valued_exact_cylinders_disjoint
    {ι : Type} (Eset : ι → Set Nat)
    (hunique : ∀ i j, i ≠ j → c6SetDisjoint (Eset i) (Eset j)) :
    ∀ i j, i ≠ j → c6SetDisjoint (Eset i) (Eset j) :=
  hunique
theorem c6_low_valued_letter_mass_sum :
    c6DyadicMass 2 + c6DyadicMass 3 = (3 : Rat) / 8 := by
  unfold c6DyadicMass
  norm_num
noncomputable def c6LowValuedWordMassSum : Nat → Rat
  | 0 => 1
  | n + 1 =>
      c6LowValuedWordMassSum n *
        (c6DyadicMass 2 + c6DyadicMass 3)
theorem c6_low_valued_word_mass_sum_formula (n : Nat) :
    c6LowValuedWordMassSum n = ((3 : Rat) / 8) ^ n := by
  induction n with
  | zero =>
      simp [c6LowValuedWordMassSum]
  | succ n ih =>
      simp [c6LowValuedWordMassSum, ih,
        c6_low_valued_letter_mass_sum, pow_succ, mul_comm]
structure C6LowValuedTailBank (n : Nat) where
  words : Finset C6LowValuedWord
  all_length_n : ∀ lambda ∈ words, lambda.length = n
  cylinder : (lambda : C6LowValuedWord) → C6LowValuedExactCylinder lambda
  Eset : C6LowValuedWord → Set Nat :=
    fun lambda => {q | (cylinder lambda).cls.Contains q}
  pairwise_disjoint :
    ∀ lambda ∈ words, ∀ mu ∈ words, lambda ≠ mu →
      c6SetDisjoint (Eset lambda) (Eset mu)
structure C6C7LowValuedTailCylinderSupply (n : Nat) where
  words : Finset C6LowValuedWord
  all_length_n : ∀ lambda ∈ words, lambda.length = n
  cylinder : (lambda : C6LowValuedWord) → C6LowValuedExactCylinder lambda
  pairwise_disjoint :
    ∀ lambda ∈ words, ∀ mu ∈ words, lambda ≠ mu →
      c6SetDisjoint
        {q | (cylinder lambda).cls.Contains q}
        {q | (cylinder mu).cls.Contains q}
def c6_low_valued_tail_bank_of_c7_supply
    (n : Nat) (supply : C6C7LowValuedTailCylinderSupply n) :
    C6LowValuedTailBank n where
  words := supply.words
  all_length_n := supply.all_length_n
  cylinder := supply.cylinder
  pairwise_disjoint := supply.pairwise_disjoint
theorem c6_low_valued_tail_bank_density (n : Nat) :
    c6LowValuedWordMassSum n = ((3 : Rat) / 8) ^ n :=
  c6_low_valued_word_mass_sum_formula n
structure C6LowValuedBinaryRealizability (n : Nat) where
  bank : C6LowValuedTailBank n
  every_word_realized :
    ∀ lambda ∈ bank.words,
      ∃ q, 0 < q ∧ q % 2 = 1 ∧ (bank.cylinder lambda).cls.Contains q
def c6_low_valued_binary_realizability
    (n : Nat) (bank : C6LowValuedTailBank n) :
    C6LowValuedBinaryRealizability n where
  bank := bank
  every_word_realized := by
    intro lambda _hlambda
    exact c6_low_valued_exact_cylinder_nonempty lambda (bank.cylinder lambda)
def c6_binary_realizability_of_c7_supply
    (n : Nat) (supply : C6C7LowValuedTailCylinderSupply n) :
    C6LowValuedBinaryRealizability n :=
  c6_low_valued_binary_realizability n
    (c6_low_valued_tail_bank_of_c7_supply n supply)

noncomputable def c11CheapDyadicMass (e : Nat) : Rat :=
  (1 : Rat) / (2 ^ e : Rat)
structure C11CheapOddResidueClass where
  exponent : Nat
  residue : Nat
  residue_odd : residue % 2 = 1
def C11CheapOddResidueClass.Contains (cls : C11CheapOddResidueClass)
    (q : Nat) : Prop :=
  Nat.ModEq (2 ^ cls.exponent) q cls.residue
noncomputable def C11CheapOddResidueClass.oddDensity
    (cls : C11CheapOddResidueClass) : Rat :=
  c11CheapDyadicMass (cls.exponent - 1)
theorem c11Cheap_one_class_density
    (cls : C11CheapOddResidueClass) :
    cls.oddDensity = c11CheapDyadicMass (cls.exponent - 1) := rfl
theorem c11Cheap_double_dyadic_mass (a : Nat) (ha : 1 <= a) :
    c11CheapDyadicMass a + c11CheapDyadicMass a =
      c11CheapDyadicMass (a - 1) := by
  unfold c11CheapDyadicMass
  have hidx : a = (a - 1) + 1 := by omega
  rw [hidx, pow_add]
  norm_num
  have hpos : (2 : Rat) ^ (a - 1) ≠ 0 := pow_ne_zero (a - 1) (by norm_num)
  field_simp [hpos]
  norm_num
theorem c11Cheap_pow_two_even_of_pos (k : Nat) (hk : 1 <= k) :
    2 ^ k % 2 = 0 := by
  cases k with
  | zero => omega
  | succ k =>
      rw [Nat.pow_succ]
      simp [Nat.mul_comm]
theorem c11Cheap_mul_pow_two_even_of_pos (a k : Nat) (hk : 1 <= k) :
    (a * 2 ^ k) % 2 = 0 := by
  have hpow := c11Cheap_pow_two_even_of_pos k hk
  rw [Nat.mul_mod, hpow]
  norm_num
theorem c11Cheap_modEq_pow_two_pred
    {q r k : Nat} (h : Nat.ModEq (2 ^ (k + 1)) q r) :
    Nat.ModEq (2 ^ k) q r := by
  unfold Nat.ModEq at h ⊢
  exact Nat.ModEq.of_dvd (by exact Nat.pow_dvd_pow 2 (by omega)) h
theorem c11Cheap_pow_three_odd (n : Nat) :
    3 ^ n % 2 = 1 := by
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih]
theorem c11Cheap_odd_half_modulus_not_zero
    (k a : Nat) (ha : a % 2 = 1) :
    ¬ Nat.ModEq (2 ^ (k + 1)) 0 (2 ^ k * a) := by
  intro h
  have hrewrite : Nat.ModEq (2 ^ k * 2) (2 ^ k * 0) (2 ^ k * a) := by
    simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  have hcancel : Nat.ModEq 2 0 a :=
    Nat.ModEq.mul_left_cancel' (pow_ne_zero k (by norm_num : (2 : Nat) ≠ 0)) hrewrite
  unfold Nat.ModEq at hcancel
  have hz : 0 % 2 = 0 := by norm_num
  rw [hz, ha] at hcancel
  omega
theorem c11Cheap_three_mul_odd_not_modEq_four
    (a : Nat) (ha : a % 2 = 1) :
    ¬ Nat.ModEq 4 (a * 3) a := by
  intro h
  unfold Nat.ModEq at h
  have hcases : a % 4 = 1 ∨ a % 4 = 3 :=
    (Nat.odd_mod_four_iff).mp ha
  rcases hcases with h1 | h3
  · rw [Nat.mul_mod, h1] at h
    norm_num at h
  · rw [Nat.mul_mod, h3] at h
    norm_num at h
theorem c11Cheap_dyadic_mass_add_next (a : Nat) :
    c11CheapDyadicMass a + c11CheapDyadicMass (a + 1) =
      3 * c11CheapDyadicMass (a + 1) := by
  unfold c11CheapDyadicMass
  have hpow : (2 : Rat) ^ (a + 1) = (2 : Rat) ^ a * 2 := by
    rw [pow_add]
    norm_num
  rw [hpow]
  have hpos : (2 : Rat) ^ a ≠ 0 := pow_ne_zero a (by norm_num)
  field_simp [hpos]
  norm_num
theorem c11Cheap_dyadic_mass_add_shift3 (a : Nat) :
    c11CheapDyadicMass a + c11CheapDyadicMass (a + 3) =
      9 * c11CheapDyadicMass (a + 3) := by
  unfold c11CheapDyadicMass
  have hpow : (2 : Rat) ^ (a + 3) = (2 : Rat) ^ a * 8 := by
    rw [pow_add]
    norm_num
  rw [hpow]
  have hpos : (2 : Rat) ^ a ≠ 0 := pow_ne_zero a (by norm_num)
  field_simp [hpos]
  norm_num
theorem c11Cheap_ratio_K_inside_F (a : Nat) :
    (9 * c11CheapDyadicMass (a + 5)) / c11CheapDyadicMass a =
      (9 : Rat) / 32 := by
  unfold c11CheapDyadicMass
  have hpow : (2 : Rat) ^ (a + 5) = (2 : Rat) ^ a * 32 := by
    rw [pow_add]
    norm_num
  rw [hpow]
  have hpos : (2 : Rat) ^ a ≠ 0 := pow_ne_zero a (by norm_num)
  field_simp [hpos]
def c11CheapL1ImmediateResonanceClass (n : Nat) : C11CheapOddResidueClass where
  exponent := 2 * n + 2
  residue := 1 + 2 ^ (2 * n + 1)
  residue_odd := by
    have hpowEven : 2 ^ (2 * n + 1) % 2 = 0 :=
      c11Cheap_pow_two_even_of_pos (2 * n + 1) (by omega)
    omega
def c11CheapL1LowValuedClass (n : Nat) : C11CheapOddResidueClass where
  exponent := 2 * n + 2
  residue := 1
  residue_odd := by norm_num
def c11CheapL1BranchClass (n : Nat) : C11CheapOddResidueClass where
  exponent := 2 * n + 1
  residue := 1
  residue_odd := by norm_num
theorem c11Cheap_L1_immediate_resonance_density (n : Nat) :
    (c11CheapL1ImmediateResonanceClass n).oddDensity =
      c11CheapDyadicMass (2 * n + 1) := by
  unfold C11CheapOddResidueClass.oddDensity c11CheapL1ImmediateResonanceClass
  change c11CheapDyadicMass ((2 * n + 2) - 1) =
    c11CheapDyadicMass (2 * n + 1)
  rw [show (2 * n + 2) - 1 = 2 * n + 1 by omega]
theorem c11Cheap_L1_low_valued_density (n : Nat) :
    (c11CheapL1LowValuedClass n).oddDensity =
      c11CheapDyadicMass (2 * n + 1) := by
  unfold C11CheapOddResidueClass.oddDensity c11CheapL1LowValuedClass
  change c11CheapDyadicMass ((2 * n + 2) - 1) =
    c11CheapDyadicMass (2 * n + 1)
  rw [show (2 * n + 2) - 1 = 2 * n + 1 by omega]
theorem c11Cheap_L1_branch_density (n : Nat) :
    (c11CheapL1BranchClass n).oddDensity =
      c11CheapDyadicMass (2 * n) := by
  unfold C11CheapOddResidueClass.oddDensity c11CheapL1BranchClass
  change c11CheapDyadicMass ((2 * n + 1) - 1) =
    c11CheapDyadicMass (2 * n)
  rw [show (2 * n + 1) - 1 = 2 * n by omega]
theorem c11Cheap_L1_first_resonance_mass_split (n : Nat) :
    (c11CheapL1LowValuedClass n).oddDensity +
      (c11CheapL1ImmediateResonanceClass n).oddDensity =
        (c11CheapL1BranchClass n).oddDensity := by
  rw [c11Cheap_L1_low_valued_density,
    c11Cheap_L1_immediate_resonance_density,
    c11Cheap_L1_branch_density]
  exact c11Cheap_double_dyadic_mass (2 * n + 1) (by omega)
theorem c11Cheap_L1_halves_distinct (n : Nat) :
    (c11CheapL1LowValuedClass n).residue ≠
      (c11CheapL1ImmediateResonanceClass n).residue := by
  unfold c11CheapL1LowValuedClass c11CheapL1ImmediateResonanceClass
  change 1 ≠ 1 + 2 ^ (2 * n + 1)
  have hpos : 0 < 2 ^ (2 * n + 1) := pow_pos (by norm_num) _
  omega
theorem c11Cheap_L1_low_subset_branch (n q : Nat)
    (hq : (c11CheapL1LowValuedClass n).Contains q) :
    (c11CheapL1BranchClass n).Contains q := by
  unfold C11CheapOddResidueClass.Contains at hq ⊢
  change Nat.ModEq (2 ^ (2 * n + 2)) q 1 at hq
  change Nat.ModEq (2 ^ (2 * n + 1)) q 1
  exact c11Cheap_modEq_pow_two_pred hq
theorem c11Cheap_L1_immediate_subset_branch (n q : Nat)
    (hq : (c11CheapL1ImmediateResonanceClass n).Contains q) :
    (c11CheapL1BranchClass n).Contains q := by
  unfold C11CheapOddResidueClass.Contains at hq ⊢
  change Nat.ModEq (2 ^ (2 * n + 2)) q (1 + 2 ^ (2 * n + 1)) at hq
  change Nat.ModEq (2 ^ (2 * n + 1)) q 1
  have hcoarse : Nat.ModEq (2 ^ (2 * n + 1)) q
      (1 + 2 ^ (2 * n + 1)) :=
    c11Cheap_modEq_pow_two_pred hq
  have hres : Nat.ModEq (2 ^ (2 * n + 1))
      (1 + 2 ^ (2 * n + 1)) 1 := by
    exact Nat.ModEq.symm (Nat.modEq_iff_dvd.mpr (by use 1; omega))
  exact Nat.ModEq.trans hcoarse hres
theorem c11Cheap_L1_halves_disjoint (n q : Nat)
    (hlow : (c11CheapL1LowValuedClass n).Contains q)
    (hhi : (c11CheapL1ImmediateResonanceClass n).Contains q) :
    False := by
  unfold C11CheapOddResidueClass.Contains at hlow hhi
  change Nat.ModEq (2 ^ (2 * n + 2)) q 1 at hlow
  change Nat.ModEq (2 ^ (2 * n + 2)) q (1 + 2 ^ (2 * n + 1)) at hhi
  have hres : Nat.ModEq (2 ^ (2 * n + 2)) 1
      (1 + 2 ^ (2 * n + 1)) := Nat.ModEq.trans (Nat.ModEq.symm hlow) hhi
  have hres' : Nat.ModEq (2 ^ (2 * n + 2)) (1 + 0)
      (1 + 2 ^ (2 * n + 1)) := by simpa using hres
  have hcancel : Nat.ModEq (2 ^ (2 * n + 2)) 0 (2 ^ (2 * n + 1)) :=
    Nat.ModEq.add_left_cancel' 1 hres'
  unfold Nat.ModEq at hcancel
  have hhalf_mod : 2 ^ (2 * n + 1) % 2 ^ (2 * n + 2) =
      2 ^ (2 * n + 1) := by
    apply Nat.mod_eq_of_lt
    have hpowpos : 0 < 2 ^ (2 * n + 1) := pow_pos (by norm_num) _
    have htwice : 2 ^ (2 * n + 2) = 2 * 2 ^ (2 * n + 1) := by
      rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, pow_succ]
      ring
    omega
  rw [Nat.zero_mod, hhalf_mod] at hcancel
  have hpos : 0 < 2 ^ (2 * n + 1) := pow_pos (by norm_num) _
  omega
def c11CheapL2LowValuedClass (n : Nat) (hn : 1 <= n) :
    C11CheapOddResidueClass where
  exponent := 2 * n + 3
  residue := 1 + 3 ^ n * 2 ^ (2 * n)
  residue_odd := by
    have hpowEven : (3 ^ n * 2 ^ (2 * n)) % 2 = 0 :=
      c11Cheap_mul_pow_two_even_of_pos (3 ^ n) (2 * n) (by omega)
    omega
def c11CheapL2ImmediateResonanceClass (n : Nat) (hn : 1 <= n) :
    C11CheapOddResidueClass where
  exponent := 2 * n + 3
  residue := 1 + 3 ^ n * 2 ^ (2 * n) + 2 ^ (2 * n + 2)
  residue_odd := by
    have hbase : (3 ^ n * 2 ^ (2 * n)) % 2 = 0 :=
      c11Cheap_mul_pow_two_even_of_pos (3 ^ n) (2 * n) (by omega)
    have hshift : 2 ^ (2 * n + 2) % 2 = 0 :=
      c11Cheap_pow_two_even_of_pos (2 * n + 2) (by omega)
    omega
def c11CheapL2BranchClass (n : Nat) (hn : 1 <= n) :
    C11CheapOddResidueClass where
  exponent := 2 * n + 2
  residue := 1 + 3 ^ n * 2 ^ (2 * n)
  residue_odd := (c11CheapL2LowValuedClass n hn).residue_odd
theorem c11Cheap_L2_immediate_resonance_density (n : Nat) (hn : 1 <= n) :
    (c11CheapL2ImmediateResonanceClass n hn).oddDensity =
      c11CheapDyadicMass (2 * n + 2) := by
  unfold C11CheapOddResidueClass.oddDensity c11CheapL2ImmediateResonanceClass
  change c11CheapDyadicMass ((2 * n + 3) - 1) =
    c11CheapDyadicMass (2 * n + 2)
  rw [show (2 * n + 3) - 1 = 2 * n + 2 by omega]
theorem c11Cheap_L2_low_valued_density (n : Nat) (hn : 1 <= n) :
    (c11CheapL2LowValuedClass n hn).oddDensity =
      c11CheapDyadicMass (2 * n + 2) := by
  unfold C11CheapOddResidueClass.oddDensity c11CheapL2LowValuedClass
  change c11CheapDyadicMass ((2 * n + 3) - 1) =
    c11CheapDyadicMass (2 * n + 2)
  rw [show (2 * n + 3) - 1 = 2 * n + 2 by omega]
theorem c11Cheap_L2_branch_density (n : Nat) (hn : 1 <= n) :
    (c11CheapL2BranchClass n hn).oddDensity =
      c11CheapDyadicMass (2 * n + 1) := by
  unfold C11CheapOddResidueClass.oddDensity c11CheapL2BranchClass
  change c11CheapDyadicMass ((2 * n + 2) - 1) =
    c11CheapDyadicMass (2 * n + 1)
  rw [show (2 * n + 2) - 1 = 2 * n + 1 by omega]
theorem c11Cheap_L2_first_resonance_mass_split (n : Nat) (hn : 1 <= n) :
    (c11CheapL2LowValuedClass n hn).oddDensity +
      (c11CheapL2ImmediateResonanceClass n hn).oddDensity =
        (c11CheapL2BranchClass n hn).oddDensity := by
  rw [c11Cheap_L2_low_valued_density n hn,
    c11Cheap_L2_immediate_resonance_density n hn,
    c11Cheap_L2_branch_density n hn]
  exact c11Cheap_double_dyadic_mass (2 * n + 2) (by omega)
theorem c11Cheap_L2_halves_distinct (n : Nat) (hn : 1 <= n) :
    (c11CheapL2LowValuedClass n hn).residue ≠
      (c11CheapL2ImmediateResonanceClass n hn).residue := by
  unfold c11CheapL2LowValuedClass c11CheapL2ImmediateResonanceClass
  change 1 + 3 ^ n * 2 ^ (2 * n) ≠
    1 + 3 ^ n * 2 ^ (2 * n) + 2 ^ (2 * n + 2)
  have hpos : 0 < 2 ^ (2 * n + 2) := pow_pos (by norm_num) _
  omega
theorem c11Cheap_L2_low_subset_branch (n q : Nat) (hn : 1 <= n)
    (hq : (c11CheapL2LowValuedClass n hn).Contains q) :
    (c11CheapL2BranchClass n hn).Contains q := by
  unfold C11CheapOddResidueClass.Contains at hq ⊢
  change Nat.ModEq (2 ^ (2 * n + 3)) q
    (1 + 3 ^ n * 2 ^ (2 * n)) at hq
  change Nat.ModEq (2 ^ (2 * n + 2)) q
    (1 + 3 ^ n * 2 ^ (2 * n))
  exact c11Cheap_modEq_pow_two_pred hq
theorem c11Cheap_L2_immediate_subset_branch (n q : Nat) (hn : 1 <= n)
    (hq : (c11CheapL2ImmediateResonanceClass n hn).Contains q) :
    (c11CheapL2BranchClass n hn).Contains q := by
  unfold C11CheapOddResidueClass.Contains at hq ⊢
  change Nat.ModEq (2 ^ (2 * n + 3)) q
    (1 + 3 ^ n * 2 ^ (2 * n) + 2 ^ (2 * n + 2)) at hq
  change Nat.ModEq (2 ^ (2 * n + 2)) q
    (1 + 3 ^ n * 2 ^ (2 * n))
  have hcoarse : Nat.ModEq (2 ^ (2 * n + 2)) q
      (1 + 3 ^ n * 2 ^ (2 * n) + 2 ^ (2 * n + 2)) :=
    c11Cheap_modEq_pow_two_pred hq
  have hres : Nat.ModEq (2 ^ (2 * n + 2))
      (1 + 3 ^ n * 2 ^ (2 * n) + 2 ^ (2 * n + 2))
      (1 + 3 ^ n * 2 ^ (2 * n)) := by
    exact Nat.ModEq.symm (Nat.modEq_iff_dvd.mpr (by use 1; omega))
  exact Nat.ModEq.trans hcoarse hres
theorem c11Cheap_L2_halves_disjoint (n q : Nat) (hn : 1 <= n)
    (hlow : (c11CheapL2LowValuedClass n hn).Contains q)
    (hhi : (c11CheapL2ImmediateResonanceClass n hn).Contains q) :
    False := by
  unfold C11CheapOddResidueClass.Contains at hlow hhi
  change Nat.ModEq (2 ^ (2 * n + 3)) q
    (1 + 3 ^ n * 2 ^ (2 * n)) at hlow
  change Nat.ModEq (2 ^ (2 * n + 3)) q
    (1 + 3 ^ n * 2 ^ (2 * n) + 2 ^ (2 * n + 2)) at hhi
  have hres : Nat.ModEq (2 ^ (2 * n + 3))
      (1 + 3 ^ n * 2 ^ (2 * n))
      (1 + 3 ^ n * 2 ^ (2 * n) + 2 ^ (2 * n + 2)) :=
    Nat.ModEq.trans (Nat.ModEq.symm hlow) hhi
  let a := 1 + 3 ^ n * 2 ^ (2 * n)
  have hres' : Nat.ModEq (2 ^ (2 * n + 3)) (a + 0)
      (a + 2 ^ (2 * n + 2)) := by simpa [a] using hres
  have hcancel : Nat.ModEq (2 ^ (2 * n + 3)) 0 (2 ^ (2 * n + 2)) :=
    Nat.ModEq.add_left_cancel' a hres'
  unfold Nat.ModEq at hcancel
  have hhalf_mod : 2 ^ (2 * n + 2) % 2 ^ (2 * n + 3) =
      2 ^ (2 * n + 2) := by
    apply Nat.mod_eq_of_lt
    have hpowpos : 0 < 2 ^ (2 * n + 2) := pow_pos (by norm_num) _
    have htwice : 2 ^ (2 * n + 3) = 2 * 2 ^ (2 * n + 2) := by
      rw [show 2 * n + 3 = (2 * n + 2) + 1 by omega, pow_succ]
      ring
    omega
  rw [Nat.zero_mod, hhalf_mod] at hcancel
  have hpos : 0 < 2 ^ (2 * n + 2) := pow_pos (by norm_num) _
  omega
structure C11CheapL1ExactResonanceResidue (n h : Nat) where
  a : Nat
  a_odd : a % 2 = 1
def c11CheapL1ExactResonanceClass
    (n h : Nat) (res : C11CheapL1ExactResonanceResidue n h) :
    C11CheapOddResidueClass where
  exponent := 2 * n + h + 1
  residue := 1 + 2 ^ (2 * n + 1) * res.a
  residue_odd := by
    have hpowEven : 2 ^ (2 * n + 1) % 2 = 0 :=
      c11Cheap_pow_two_even_of_pos (2 * n + 1) (by omega)
    have hmulEven : (2 ^ (2 * n + 1) * res.a) % 2 = 0 := by
      rw [Nat.mul_mod, hpowEven]
      norm_num
    omega
theorem c11Cheap_L1_exact_resonance_density
    (n h : Nat) (_hn : 1 <= n) (_hh : 2 <= h)
    (res : C11CheapL1ExactResonanceResidue n h) :
    (c11CheapL1ExactResonanceClass n h res).oddDensity =
      c11CheapDyadicMass (2 * n + h) := by
  unfold C11CheapOddResidueClass.oddDensity c11CheapL1ExactResonanceClass
  change c11CheapDyadicMass ((2 * n + h + 1) - 1) =
    c11CheapDyadicMass (2 * n + h)
  rw [show (2 * n + h + 1) - 1 = 2 * n + h by omega]
structure C11CheapL2ExactResonanceResidue (n h : Nat) where
  a : Nat
  a_odd : a % 2 = 1
def c11CheapL2ExactResonanceClass
    (n h : Nat) (hn : 1 <= n)
    (res : C11CheapL2ExactResonanceResidue n h) :
    C11CheapOddResidueClass where
  exponent := 2 * n + h + 2
  residue := 1 + 3 ^ n * 2 ^ (2 * n) + 2 ^ (2 * n + 2) * res.a
  residue_odd := by
    have hbase : (3 ^ n * 2 ^ (2 * n)) % 2 = 0 :=
      c11Cheap_mul_pow_two_even_of_pos (3 ^ n) (2 * n) (by omega)
    have htail : (2 ^ (2 * n + 2) * res.a) % 2 = 0 := by
      have hpow : 2 ^ (2 * n + 2) % 2 = 0 :=
        c11Cheap_pow_two_even_of_pos (2 * n + 2) (by omega)
      rw [Nat.mul_mod, hpow]
      norm_num
    omega
theorem c11Cheap_L2_exact_resonance_density
    (n h : Nat) (hn : 1 <= n) (_hh : 2 <= h)
    (res : C11CheapL2ExactResonanceResidue n h) :
    (c11CheapL2ExactResonanceClass n h hn res).oddDensity =
      c11CheapDyadicMass (2 * n + h + 1) := by
  unfold C11CheapOddResidueClass.oddDensity c11CheapL2ExactResonanceClass
  change c11CheapDyadicMass ((2 * n + h + 2) - 1) =
    c11CheapDyadicMass (2 * n + h + 1)
  rw [show (2 * n + h + 2) - 1 = 2 * n + h + 1 by omega]
structure C11CheapL1TailResidue (n H : Nat) where
  b : Nat
  b_odd : b % 2 = 1
def c11CheapL1TailClass (n H : Nat) (tail : C11CheapL1TailResidue n H) :
    C11CheapOddResidueClass where
  exponent := 2 * n + H
  residue := 1 + 2 ^ (2 * n + 1) * tail.b
  residue_odd := by
    have hpowEven : 2 ^ (2 * n + 1) % 2 = 0 :=
      c11Cheap_pow_two_even_of_pos (2 * n + 1) (by omega)
    have hmulEven : (2 ^ (2 * n + 1) * tail.b) % 2 = 0 := by
      rw [Nat.mul_mod, hpowEven]
      norm_num
    omega
theorem c11Cheap_L1_tail_density
    (n H : Nat) (_hn : 1 <= n) (_hH : 2 <= H)
    (tail : C11CheapL1TailResidue n H) :
    (c11CheapL1TailClass n H tail).oddDensity =
      c11CheapDyadicMass (2 * n + H - 1) := by
  unfold C11CheapOddResidueClass.oddDensity c11CheapL1TailClass
  change c11CheapDyadicMass ((2 * n + H) - 1) =
    c11CheapDyadicMass (2 * n + H - 1)
  rfl
structure C11CheapL2TailResidue (n H : Nat) where
  b : Nat
  b_odd : b % 2 = 1
def c11CheapL2TailClass
    (n H : Nat) (hn : 1 <= n) (tail : C11CheapL2TailResidue n H) :
    C11CheapOddResidueClass where
  exponent := 2 * n + H + 1
  residue := 1 + 3 ^ n * 2 ^ (2 * n) + 2 ^ (2 * n + 2) * tail.b
  residue_odd := by
    have hbase : (3 ^ n * 2 ^ (2 * n)) % 2 = 0 :=
      c11Cheap_mul_pow_two_even_of_pos (3 ^ n) (2 * n) (by omega)
    have hshift : (2 ^ (2 * n + 2) * tail.b) % 2 = 0 := by
      have hpow : 2 ^ (2 * n + 2) % 2 = 0 :=
        c11Cheap_pow_two_even_of_pos (2 * n + 2) (by omega)
      rw [Nat.mul_mod, hpow]
      norm_num
    omega
theorem c11Cheap_L2_tail_density
    (n H : Nat) (hn : 1 <= n) (_hH : 2 <= H)
    (tail : C11CheapL2TailResidue n H) :
    (c11CheapL2TailClass n H hn tail).oddDensity =
      c11CheapDyadicMass (2 * n + H) := by
  unfold C11CheapOddResidueClass.oddDensity c11CheapL2TailClass
  change c11CheapDyadicMass ((2 * n + H + 1) - 1) =
    c11CheapDyadicMass (2 * n + H)
  rw [show (2 * n + H + 1) - 1 = 2 * n + H by omega]
structure C11CheapL1TailDecomposition (n H : Nat) where
  tail_residue : C11CheapL1TailResidue n H
  exact_residue : ∀ h, H <= h → C11CheapL1ExactResonanceResidue n h
  pairwise_disjoint_exact_depths : Prop
  union_exact_depths_tail : Prop
  tail_density :
    (c11CheapL1TailClass n H tail_residue).oddDensity =
      c11CheapDyadicMass (2 * n + H - 1)
def c11Cheap_L1_tail_decomposition
    (n H : Nat) (hn : 1 <= n) (hH : 2 <= H)
    (tail : C11CheapL1TailResidue n H)
    (exact : ∀ h, H <= h → C11CheapL1ExactResonanceResidue n h)
    (hpairwise : Prop) (hunion : Prop) :
    C11CheapL1TailDecomposition n H where
  tail_residue := tail
  exact_residue := exact
  pairwise_disjoint_exact_depths := hpairwise
  union_exact_depths_tail := hunion
  tail_density := c11Cheap_L1_tail_density n H hn hH tail
structure C11CheapL2TailDecomposition (n H : Nat) (hn : 1 <= n) where
  tail_residue : C11CheapL2TailResidue n H
  exact_residue : ∀ h, H <= h → C11CheapL2ExactResonanceResidue n h
  pairwise_disjoint_exact_depths : Prop
  union_exact_depths_tail : Prop
  tail_density :
    (c11CheapL2TailClass n H hn tail_residue).oddDensity =
      c11CheapDyadicMass (2 * n + H)
def c11Cheap_L2_tail_decomposition
    (n H : Nat) (hn : 1 <= n) (hH : 2 <= H)
    (tail : C11CheapL2TailResidue n H)
    (exact : ∀ h, H <= h → C11CheapL2ExactResonanceResidue n h)
    (hpairwise : Prop) (hunion : Prop) :
    C11CheapL2TailDecomposition n H hn where
  tail_residue := tail
  exact_residue := exact
  pairwise_disjoint_exact_depths := hpairwise
  union_exact_depths_tail := hunion
  tail_density := c11Cheap_L2_tail_density n H hn hH tail
def c11CheapLargeLengthBranchClass (n : Nat) (hn : 1 <= n) :
    C11CheapOddResidueClass where
  exponent := 2 * n + 2
  residue := 1 + 3 ^ (n - 1) * 2 ^ (2 * n)
  residue_odd := by
    have hbase : (3 ^ (n - 1) * 2 ^ (2 * n)) % 2 = 0 :=
      c11Cheap_mul_pow_two_even_of_pos (3 ^ (n - 1)) (2 * n) (by omega)
    omega
def c11CheapChainClass (n : Nat) (_hn : 1 <= n) :
    C11CheapOddResidueClass where
  exponent := 2 * n
  residue := 1
  residue_odd := by norm_num
theorem c11Cheap_chain_contains_iff_begins
    (n q : Nat) (hn : 1 <= n) :
    (c11CheapChainClass n hn).Contains q ↔
      c6BeginsCheapChainLength n q := by
  unfold C11CheapOddResidueClass.Contains c11CheapChainClass
  exact (c6_cheap_chain_congruence_criterion n q hn).symm
theorem c11Cheap_L1_branch_contains_iff_c6
    (n q : Nat) (hn : 1 <= n) (hchain : c6BeginsCheapChainLength n q) :
    (c11CheapL1BranchClass n).Contains q ↔
      ∃ k t, q = 1 + 2 ^ (2 * n) * k ∧ k = 2 * t := by
  unfold C11CheapOddResidueClass.Contains c11CheapL1BranchClass
  exact c6_cheap_prefix_first_deviation_Ln1_iff n q hn hchain
theorem c11Cheap_L2_branch_contains_iff_c6
    (n q : Nat) (hn : 1 <= n) (hchain : c6BeginsCheapChainLength n q) :
    (c11CheapL2BranchClass n hn).Contains q ↔
      ∃ k, q = 1 + 2 ^ (2 * n) * k ∧ Nat.ModEq 4 k (3 ^ n) := by
  unfold C11CheapOddResidueClass.Contains c11CheapL2BranchClass
  exact c6_cheap_prefix_first_deviation_Ln2_iff n q hn hchain
theorem c11Cheap_large_length_contains_iff_c6
    (n q : Nat) (hn : 1 <= n) (hchain : c6BeginsCheapChainLength n q) :
    (c11CheapLargeLengthBranchClass n hn).Contains q ↔
      ∃ k, q = 1 + 2 ^ (2 * n) * k ∧ Nat.ModEq 4 k (3 ^ (n - 1)) := by
  unfold C11CheapOddResidueClass.Contains c11CheapLargeLengthBranchClass
  exact c6_cheap_prefix_first_deviation_LnGe3_iff n q hn hchain
theorem c11Cheap_large_length_branch_density (n : Nat) (hn : 1 <= n) :
    (c11CheapLargeLengthBranchClass n hn).oddDensity =
      c11CheapDyadicMass (2 * n + 1) := by
  unfold C11CheapOddResidueClass.oddDensity c11CheapLargeLengthBranchClass
  change c11CheapDyadicMass ((2 * n + 2) - 1) =
    c11CheapDyadicMass (2 * n + 1)
  rw [show (2 * n + 2) - 1 = 2 * n + 1 by omega]
theorem c11Cheap_large_length_subset_chain
    (n q : Nat) (hn : 1 <= n)
    (hq : (c11CheapLargeLengthBranchClass n hn).Contains q) :
    (c11CheapChainClass n hn).Contains q := by
  unfold C11CheapOddResidueClass.Contains at hq ⊢
  change Nat.ModEq (2 ^ (2 * n + 2)) q
    (1 + 3 ^ (n - 1) * 2 ^ (2 * n)) at hq
  change Nat.ModEq (2 ^ (2 * n)) q 1
  have hcoarse1 : Nat.ModEq (2 ^ (2 * n + 1)) q
      (1 + 3 ^ (n - 1) * 2 ^ (2 * n)) :=
    c11Cheap_modEq_pow_two_pred hq
  have hcoarse2 : Nat.ModEq (2 ^ (2 * n)) q
      (1 + 3 ^ (n - 1) * 2 ^ (2 * n)) :=
    c11Cheap_modEq_pow_two_pred hcoarse1
  have hres : Nat.ModEq (2 ^ (2 * n))
      (1 + 3 ^ (n - 1) * 2 ^ (2 * n)) 1 := by
    exact Nat.ModEq.symm (Nat.modEq_iff_dvd.mpr (by
      use 3 ^ (n - 1)
      simp [Nat.mul_comm]))
  exact Nat.ModEq.trans hcoarse2 hres
theorem c11Cheap_L1_branch_subset_chain
    (n q : Nat) (hn : 1 <= n)
    (hq : (c11CheapL1BranchClass n).Contains q) :
    (c11CheapChainClass n hn).Contains q := by
  unfold C11CheapOddResidueClass.Contains at hq ⊢
  change Nat.ModEq (2 ^ (2 * n + 1)) q 1 at hq
  change Nat.ModEq (2 ^ (2 * n)) q 1
  exact c11Cheap_modEq_pow_two_pred hq
theorem c11Cheap_L2_branch_subset_chain
    (n q : Nat) (hn : 1 <= n)
    (hq : (c11CheapL2BranchClass n hn).Contains q) :
    (c11CheapChainClass n hn).Contains q := by
  unfold C11CheapOddResidueClass.Contains at hq ⊢
  change Nat.ModEq (2 ^ (2 * n + 2)) q
    (1 + 3 ^ n * 2 ^ (2 * n)) at hq
  change Nat.ModEq (2 ^ (2 * n)) q 1
  have hcoarse1 : Nat.ModEq (2 ^ (2 * n + 1)) q
      (1 + 3 ^ n * 2 ^ (2 * n)) :=
    c11Cheap_modEq_pow_two_pred hq
  have hcoarse2 : Nat.ModEq (2 ^ (2 * n)) q
      (1 + 3 ^ n * 2 ^ (2 * n)) :=
    c11Cheap_modEq_pow_two_pred hcoarse1
  have hres : Nat.ModEq (2 ^ (2 * n))
      (1 + 3 ^ n * 2 ^ (2 * n)) 1 := by
    exact Nat.ModEq.symm (Nat.modEq_iff_dvd.mpr (by
      use 3 ^ n
      simp [Nat.mul_comm]))
  exact Nat.ModEq.trans hcoarse2 hres
theorem c11Cheap_L1_L2_branches_disjoint
    (n q : Nat) (hn : 1 <= n)
    (h1 : (c11CheapL1BranchClass n).Contains q)
    (h2 : (c11CheapL2BranchClass n hn).Contains q) :
    False := by
  unfold C11CheapOddResidueClass.Contains at h1 h2
  change Nat.ModEq (2 ^ (2 * n + 1)) q 1 at h1
  change Nat.ModEq (2 ^ (2 * n + 2)) q
    (1 + 3 ^ n * 2 ^ (2 * n)) at h2
  have h2coarse : Nat.ModEq (2 ^ (2 * n + 1)) q
      (1 + 3 ^ n * 2 ^ (2 * n)) :=
    c11Cheap_modEq_pow_two_pred h2
  have hres : Nat.ModEq (2 ^ (2 * n + 1)) 1
      (1 + 3 ^ n * 2 ^ (2 * n)) :=
    Nat.ModEq.trans (Nat.ModEq.symm h1) h2coarse
  have hres' : Nat.ModEq (2 ^ (2 * n + 1)) (1 + 0)
      (1 + 2 ^ (2 * n) * 3 ^ n) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hres
  have hcancel : Nat.ModEq (2 ^ (2 * n + 1)) 0 (2 ^ (2 * n) * 3 ^ n) :=
    Nat.ModEq.add_left_cancel' 1 hres'
  exact c11Cheap_odd_half_modulus_not_zero (2 * n) (3 ^ n)
    (c11Cheap_pow_three_odd n) hcancel
theorem c11Cheap_L1_large_branches_disjoint
    (n q : Nat) (hn : 1 <= n)
    (h1 : (c11CheapL1BranchClass n).Contains q)
    (hlarge : (c11CheapLargeLengthBranchClass n hn).Contains q) :
    False := by
  unfold C11CheapOddResidueClass.Contains at h1 hlarge
  change Nat.ModEq (2 ^ (2 * n + 1)) q 1 at h1
  change Nat.ModEq (2 ^ (2 * n + 2)) q
    (1 + 3 ^ (n - 1) * 2 ^ (2 * n)) at hlarge
  have hlarge_coarse : Nat.ModEq (2 ^ (2 * n + 1)) q
      (1 + 3 ^ (n - 1) * 2 ^ (2 * n)) :=
    c11Cheap_modEq_pow_two_pred hlarge
  have hres : Nat.ModEq (2 ^ (2 * n + 1)) 1
      (1 + 3 ^ (n - 1) * 2 ^ (2 * n)) :=
    Nat.ModEq.trans (Nat.ModEq.symm h1) hlarge_coarse
  have hres' : Nat.ModEq (2 ^ (2 * n + 1)) (1 + 0)
      (1 + 2 ^ (2 * n) * 3 ^ (n - 1)) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hres
  have hcancel : Nat.ModEq (2 ^ (2 * n + 1)) 0
      (2 ^ (2 * n) * 3 ^ (n - 1)) :=
    Nat.ModEq.add_left_cancel' 1 hres'
  exact c11Cheap_odd_half_modulus_not_zero (2 * n) (3 ^ (n - 1))
    (c11Cheap_pow_three_odd (n - 1)) hcancel
theorem c11Cheap_L2_large_branches_disjoint
    (n q : Nat) (hn : 1 <= n)
    (h2 : (c11CheapL2BranchClass n hn).Contains q)
    (hlarge : (c11CheapLargeLengthBranchClass n hn).Contains q) :
    False := by
  unfold C11CheapOddResidueClass.Contains at h2 hlarge
  change Nat.ModEq (2 ^ (2 * n + 2)) q
    (1 + 3 ^ n * 2 ^ (2 * n)) at h2
  change Nat.ModEq (2 ^ (2 * n + 2)) q
    (1 + 3 ^ (n - 1) * 2 ^ (2 * n)) at hlarge
  have hres : Nat.ModEq (2 ^ (2 * n + 2))
      (1 + 3 ^ n * 2 ^ (2 * n))
      (1 + 3 ^ (n - 1) * 2 ^ (2 * n)) :=
    Nat.ModEq.trans (Nat.ModEq.symm h2) hlarge
  have hfactor : 3 ^ n = 3 ^ (n - 1) * 3 := by
    cases n with
    | zero => omega
    | succ m =>
        simp [pow_succ, Nat.mul_comm]
  have hres' : Nat.ModEq (2 ^ (2 * n + 2))
      (1 + 2 ^ (2 * n) * (3 ^ (n - 1) * 3))
      (1 + 2 ^ (2 * n) * 3 ^ (n - 1)) := by
    simpa [hfactor, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hres
  have hcancel1 : Nat.ModEq (2 ^ (2 * n + 2))
      (2 ^ (2 * n) * (3 ^ (n - 1) * 3))
      (2 ^ (2 * n) * 3 ^ (n - 1)) :=
    Nat.ModEq.add_left_cancel' 1 hres'
  have hcancel2 : Nat.ModEq 4 (3 ^ (n - 1) * 3) (3 ^ (n - 1)) := by
    have hmodulus : 2 ^ (2 * n + 2) = 2 ^ (2 * n) * 4 := by
      rw [show 2 * n + 2 = 2 * n + 2 by rfl, pow_add]
      norm_num
    rw [hmodulus] at hcancel1
    exact Nat.ModEq.mul_left_cancel'
      (pow_ne_zero (2 * n) (by norm_num : (2 : Nat) ≠ 0)) hcancel1
  exact c11Cheap_three_mul_odd_not_modEq_four (3 ^ (n - 1))
    (c11Cheap_pow_three_odd (n - 1)) hcancel2
structure C11CheapLargeLengthNegativeGapBranch (n : Nat) (hn : 1 <= n) where
  branch : C11CheapOddResidueClass := c11CheapLargeLengthBranchClass n hn
  branch_density :
    branch.oddDensity = c11CheapDyadicMass (2 * n + 1)
  strict_negative_gap : Prop
def c11Cheap_large_length_negative_gap_branch
    (n : Nat) (hn : 1 <= n) (hgap : Prop) :
    C11CheapLargeLengthNegativeGapBranch n hn where
  branch_density := c11Cheap_large_length_branch_density n hn
  strict_negative_gap := hgap
theorem c11Cheap_chain_density (n : Nat) (hn : 1 <= n) :
    (c11CheapChainClass n hn).oddDensity =
      c11CheapDyadicMass (2 * n - 1) := by
  unfold C11CheapOddResidueClass.oddDensity c11CheapChainClass
  change c11CheapDyadicMass ((2 * n) - 1) =
    c11CheapDyadicMass (2 * n - 1)
  rfl
theorem c11Cheap_first_post_cheap_decomposition_density
    (n : Nat) (hn : 1 <= n) :
    (c11CheapL1BranchClass n).oddDensity +
      (c11CheapL2BranchClass n hn).oddDensity +
        (c11CheapLargeLengthBranchClass n hn).oddDensity =
          (c11CheapChainClass n hn).oddDensity := by
  rw [c11Cheap_L1_branch_density n,
    c11Cheap_L2_branch_density n hn,
    c11Cheap_large_length_branch_density n hn,
    c11Cheap_chain_density n hn]
  have h1 : c11CheapDyadicMass (2 * n + 1) +
      c11CheapDyadicMass (2 * n + 1) =
      c11CheapDyadicMass (2 * n) :=
    c11Cheap_double_dyadic_mass (2 * n + 1) (by omega)
  rw [add_assoc, h1]
  exact c11Cheap_double_dyadic_mass (2 * n) (by omega)
structure C11CheapFirstPostCheapDecomposition (n : Nat) (hn : 1 <= n) where
  cheap_chain : C11CheapOddResidueClass := c11CheapChainClass n hn
  branch_L1 : C11CheapOddResidueClass := c11CheapL1BranchClass n
  branch_L2 : C11CheapOddResidueClass := c11CheapL2BranchClass n hn
  branch_L_ge_three : C11CheapOddResidueClass :=
    c11CheapLargeLengthBranchClass n hn
  c6_chain_bridge :
    ∀ q, (c11CheapChainClass n hn).Contains q ↔ c6BeginsCheapChainLength n q
  c6_branch_L1_bridge :
    ∀ q, c6BeginsCheapChainLength n q →
      ((c11CheapL1BranchClass n).Contains q ↔
        ∃ k t, q = 1 + 2 ^ (2 * n) * k ∧ k = 2 * t)
  c6_branch_L2_bridge :
    ∀ q, c6BeginsCheapChainLength n q →
      ((c11CheapL2BranchClass n hn).Contains q ↔
        ∃ k, q = 1 + 2 ^ (2 * n) * k ∧ Nat.ModEq 4 k (3 ^ n))
  c6_branch_L_ge_three_bridge :
    ∀ q, c6BeginsCheapChainLength n q →
      ((c11CheapLargeLengthBranchClass n hn).Contains q ↔
        ∃ k, q = 1 + 2 ^ (2 * n) * k ∧ Nat.ModEq 4 k (3 ^ (n - 1)))
  branch_L1_density :
    branch_L1.oddDensity = c11CheapDyadicMass (2 * n)
  branch_L2_density :
    branch_L2.oddDensity = c11CheapDyadicMass (2 * n + 1)
  branch_L_ge_three_density :
    branch_L_ge_three.oddDensity = c11CheapDyadicMass (2 * n + 1)
  cheap_chain_density :
    cheap_chain.oddDensity = c11CheapDyadicMass (2 * n - 1)
  density_sum :
    branch_L1.oddDensity + branch_L2.oddDensity +
      branch_L_ge_three.oddDensity = cheap_chain.oddDensity
def c11Cheap_first_post_cheap_decomposition
    (n : Nat) (hn : 1 <= n) :
    C11CheapFirstPostCheapDecomposition n hn where
  c6_chain_bridge := fun q => c11Cheap_chain_contains_iff_begins n q hn
  c6_branch_L1_bridge := fun q hchain =>
    c11Cheap_L1_branch_contains_iff_c6 n q hn hchain
  c6_branch_L2_bridge := fun q hchain =>
    c11Cheap_L2_branch_contains_iff_c6 n q hn hchain
  c6_branch_L_ge_three_bridge := fun q hchain =>
    c11Cheap_large_length_contains_iff_c6 n q hn hchain
  branch_L1_density := c11Cheap_L1_branch_density n
  branch_L2_density := c11Cheap_L2_branch_density n hn
  branch_L_ge_three_density := c11Cheap_large_length_branch_density n hn
  cheap_chain_density := c11Cheap_chain_density n hn
  density_sum := c11Cheap_first_post_cheap_decomposition_density n hn
structure C11CheapLowValuedWord where
  entries : List Nat
  entries_one_or_two : ∀ ell ∈ entries, ell = 1 ∨ ell = 2
namespace C11CheapLowValuedWord
def length (lambda : C11CheapLowValuedWord) : Nat :=
  lambda.entries.length
def weight (lambda : C11CheapLowValuedWord) : Nat :=
  lambda.entries.sum
end C11CheapLowValuedWord
def c11CheapSetDisjoint {α : Type} (A B : Set α) : Prop :=
  ∀ x, x ∈ A → x ∈ B → False
def c11CheapPreimage {α β : Type} (Q : α → β) (A : Set β) : Set α :=
  {x | Q x ∈ A}
theorem c11Cheap_preimage_disjoint {α β : Type}
    (Q : α → β) {A B : Set β}
    (hAB : c11CheapSetDisjoint A B) :
    c11CheapSetDisjoint (c11CheapPreimage Q A) (c11CheapPreimage Q B) := by
  intro x hxA hxB
  exact hAB (Q x) hxA hxB
theorem c11Cheap_preimage_pairwise_disjoint {α β ι : Type}
    (Q : α → β) (E : ι → Set β)
    (hpair : ∀ lambda mu, lambda ≠ mu →
      c11CheapSetDisjoint (E lambda) (E mu)) :
    ∀ lambda mu, lambda ≠ mu →
      c11CheapSetDisjoint
        (c11CheapPreimage Q (E lambda))
        (c11CheapPreimage Q (E mu)) := by
  intro lambda mu hne
  exact c11Cheap_preimage_disjoint Q (hpair lambda mu hne)
def c11CheapWordOne : C11CheapLowValuedWord where
  entries := [1]
  entries_one_or_two := by
    intro ell hell
    simp at hell
    exact Or.inl hell
theorem c11CheapWordOne_length : c11CheapWordOne.length = 1 := rfl
theorem c11CheapWordOne_weight : c11CheapWordOne.weight = 1 := rfl
theorem c11Cheap_low_valued_letter_mass_sum :
    c11CheapDyadicMass 2 + c11CheapDyadicMass 3 = (3 : Rat) / 8 := by
  unfold c11CheapDyadicMass
  norm_num
noncomputable def c11CheapLowValuedWordMassSum : Nat → Rat
  | 0 => 1
  | m + 1 =>
      c11CheapLowValuedWordMassSum m *
        (c11CheapDyadicMass 2 + c11CheapDyadicMass 3)
theorem c11Cheap_low_valued_word_mass_sum_formula (m : Nat) :
    c11CheapLowValuedWordMassSum m = ((3 : Rat) / 8) ^ m := by
  induction m with
  | zero =>
      simp [c11CheapLowValuedWordMassSum]
  | succ m ih =>
      simp [c11CheapLowValuedWordMassSum, ih,
        c11Cheap_low_valued_letter_mass_sum, pow_succ, mul_comm]
structure C11CheapFTailClass (n : Nat) (lambda : C11CheapLowValuedWord) where
  cls : C11CheapOddResidueClass
  exponent_eq :
    cls.exponent = 2 * n + lambda.length + lambda.weight + 1
  nonempty : Prop
theorem c11Cheap_F_tail_density
    (n : Nat) (lambda : C11CheapLowValuedWord)
    (F : C11CheapFTailClass n lambda) :
    F.cls.oddDensity =
      c11CheapDyadicMass (2 * n + lambda.length + lambda.weight) := by
  unfold C11CheapOddResidueClass.oddDensity
  rw [F.exponent_eq]
  rw [show
    (2 * n + lambda.length + lambda.weight + 1) - 1 =
      2 * n + lambda.length + lambda.weight by omega]
structure C11CheapGTailClass (n : Nat) (lambda : C11CheapLowValuedWord) where
  cls : C11CheapOddResidueClass
  exponent_eq :
    cls.exponent = 2 * n + lambda.length + lambda.weight + 2
  nonempty : Prop
theorem c11Cheap_G_tail_density
    (n : Nat) (lambda : C11CheapLowValuedWord)
    (G : C11CheapGTailClass n lambda) :
    G.cls.oddDensity =
      c11CheapDyadicMass (2 * n + lambda.length + lambda.weight + 1) := by
  unfold C11CheapOddResidueClass.oddDensity
  rw [G.exponent_eq]
  rw [show
    (2 * n + lambda.length + lambda.weight + 2) - 1 =
      2 * n + lambda.length + lambda.weight + 1 by omega]
structure C11CheapFTailFamily (n m : Nat) where
  words : Finset C11CheapLowValuedWord
  all_length_m : ∀ lambda ∈ words, lambda.length = m
  terminal_stage : Nat → Nat
  terminal_E : C11CheapLowValuedWord → Set Nat
  F_set : C11CheapLowValuedWord → Set Nat :=
    fun lambda => c11CheapPreimage terminal_stage (terminal_E lambda)
  terminal_pairwise_disjoint :
    ∀ lambda ∈ words, ∀ mu ∈ words, lambda ≠ mu →
      c11CheapSetDisjoint (terminal_E lambda) (terminal_E mu)
  pulled_pairwise_disjoint :
    ∀ lambda ∈ words, ∀ mu ∈ words, lambda ≠ mu →
      c11CheapSetDisjoint (F_set lambda) (F_set mu)
def c11Cheap_F_tail_family
    (n m : Nat)
    (words : Finset C11CheapLowValuedWord)
    (hall : ∀ lambda ∈ words, lambda.length = m)
    (terminal_stage : Nat → Nat)
    (terminal_E : C11CheapLowValuedWord → Set Nat)
    (hterminal : ∀ lambda ∈ words, ∀ mu ∈ words, lambda ≠ mu →
      c11CheapSetDisjoint (terminal_E lambda) (terminal_E mu)) :
    C11CheapFTailFamily n m where
  words := words
  all_length_m := hall
  terminal_stage := terminal_stage
  terminal_E := terminal_E
  terminal_pairwise_disjoint := hterminal
  pulled_pairwise_disjoint := by
    intro lambda hlambda mu hmu hne
    exact c11Cheap_preimage_disjoint terminal_stage
      (hterminal lambda hlambda mu hmu hne)
structure C11CheapGTailFamily (n m : Nat) where
  words : Finset C11CheapLowValuedWord
  all_length_m : ∀ lambda ∈ words, lambda.length = m
  terminal_stage : Nat → Nat
  terminal_E : C11CheapLowValuedWord → Set Nat
  G_set : C11CheapLowValuedWord → Set Nat :=
    fun lambda => c11CheapPreimage terminal_stage (terminal_E lambda)
  terminal_pairwise_disjoint :
    ∀ lambda ∈ words, ∀ mu ∈ words, lambda ≠ mu →
      c11CheapSetDisjoint (terminal_E lambda) (terminal_E mu)
  pulled_pairwise_disjoint :
    ∀ lambda ∈ words, ∀ mu ∈ words, lambda ≠ mu →
      c11CheapSetDisjoint (G_set lambda) (G_set mu)
def c11Cheap_G_tail_family
    (n m : Nat)
    (words : Finset C11CheapLowValuedWord)
    (hall : ∀ lambda ∈ words, lambda.length = m)
    (terminal_stage : Nat → Nat)
    (terminal_E : C11CheapLowValuedWord → Set Nat)
    (hterminal : ∀ lambda ∈ words, ∀ mu ∈ words, lambda ≠ mu →
      c11CheapSetDisjoint (terminal_E lambda) (terminal_E mu)) :
    C11CheapGTailFamily n m where
  words := words
  all_length_m := hall
  terminal_stage := terminal_stage
  terminal_E := terminal_E
  terminal_pairwise_disjoint := hterminal
  pulled_pairwise_disjoint := by
    intro lambda hlambda mu hmu hne
    exact c11Cheap_preimage_disjoint terminal_stage
      (hterminal lambda hlambda mu hmu hne)
theorem c11Cheap_F_length_bank_density (n m : Nat) :
    c11CheapDyadicMass (2 * n) * c11CheapLowValuedWordMassSum m =
      c11CheapDyadicMass (2 * n) * ((3 : Rat) / 8) ^ m := by
  rw [c11Cheap_low_valued_word_mass_sum_formula]
theorem c11Cheap_G_length_bank_density (n m : Nat) :
    c11CheapDyadicMass (2 * n + 1) * c11CheapLowValuedWordMassSum m =
      c11CheapDyadicMass (2 * n + 1) * ((3 : Rat) / 8) ^ m := by
  rw [c11Cheap_low_valued_word_mass_sum_formula]
structure C11CheapK1NegativeGapBank (n : Nat) where
  class9 : C11CheapOddResidueClass
  class9_exponent : class9.exponent = 2 * n + 5
  class13 : C11CheapOddResidueClass
  class13_exponent : class13.exponent = 2 * n + 8
  terminal_c1 : Nat
  terminal_d1 : Nat
  terminal_c1_mod32 : Nat.ModEq 32 terminal_c1 class9.residue
  terminal_d1_mod32 : Nat.ModEq 32 terminal_d1 class13.residue
  terminal_c1_hits_19 : (3 * terminal_c1) % 32 = 19
  terminal_d1_hits_27 : (3 * terminal_d1) % 32 = 27
  negative_gap_9 : Prop
  negative_gap_13 : Prop
theorem c11Cheap_K1_terminal_classes_distinct_mod32
    (c1 d1 : Nat)
    (hc : (3 * c1) % 32 = 19)
    (hd : (3 * d1) % 32 = 27) :
    ¬ Nat.ModEq 32 c1 d1 := by
  intro h
  have hmul0 : Nat.ModEq 32 (c1 * 3) (d1 * 3) := Nat.ModEq.mul_right 3 h
  have hmul : Nat.ModEq 32 (3 * c1) (3 * d1) := by
    simpa [Nat.mul_comm] using hmul0
  unfold Nat.ModEq at hmul
  rw [hc, hd] at hmul
  norm_num at hmul
theorem c11Cheap_K1_classes_disjoint
    (n q : Nat) (K : C11CheapK1NegativeGapBank n)
    (h9 : K.class9.Contains q)
    (h13 : K.class13.Contains q) :
    False := by
  unfold C11CheapOddResidueClass.Contains at h9 h13
  rw [K.class9_exponent] at h9
  rw [K.class13_exponent] at h13
  have h9_32 : Nat.ModEq 32 q K.class9.residue := by
    have hpow : 32 = 2 ^ 5 := rfl
    rw [hpow]
    exact Nat.ModEq.of_dvd
      (Nat.pow_dvd_pow 2 (by omega : 5 <= 2 * n + 5)) h9
  have h13_32 : Nat.ModEq 32 q K.class13.residue := by
    have hpow : 32 = 2 ^ 5 := rfl
    rw [hpow]
    exact Nat.ModEq.of_dvd
      (Nat.pow_dvd_pow 2 (by omega : 5 <= 2 * n + 8)) h13
  have hcd : Nat.ModEq 32 K.terminal_c1 K.terminal_d1 := by
    exact Nat.ModEq.trans K.terminal_c1_mod32
      (Nat.ModEq.trans (Nat.ModEq.symm h9_32)
        (Nat.ModEq.trans h13_32 (Nat.ModEq.symm K.terminal_d1_mod32)))
  exact c11Cheap_K1_terminal_classes_distinct_mod32
    K.terminal_c1 K.terminal_d1
    K.terminal_c1_hits_19 K.terminal_d1_hits_27 hcd
theorem c11Cheap_K1_class9_density (n : Nat)
    (K : C11CheapK1NegativeGapBank n) :
    K.class9.oddDensity = c11CheapDyadicMass (2 * n + 4) := by
  unfold C11CheapOddResidueClass.oddDensity
  rw [K.class9_exponent]
  rw [show (2 * n + 5) - 1 = 2 * n + 4 by omega]
theorem c11Cheap_K1_class13_density (n : Nat)
    (K : C11CheapK1NegativeGapBank n) :
    K.class13.oddDensity = c11CheapDyadicMass (2 * n + 7) := by
  unfold C11CheapOddResidueClass.oddDensity
  rw [K.class13_exponent]
  rw [show (2 * n + 8) - 1 = 2 * n + 7 by omega]
theorem c11Cheap_K1_total_density (n : Nat)
    (K : C11CheapK1NegativeGapBank n) :
    K.class9.oddDensity + K.class13.oddDensity =
      9 * c11CheapDyadicMass (2 * n + 7) := by
  rw [c11Cheap_K1_class9_density n K, c11Cheap_K1_class13_density n K]
  rw [show 2 * n + 7 = 2 * n + 4 + 3 by omega]
  exact c11Cheap_dyadic_mass_add_shift3 (2 * n + 4)
theorem c11Cheap_K1_ratio_inside_F_one (n : Nat) :
    (9 * c11CheapDyadicMass (2 * n + 7)) /
        c11CheapDyadicMass (2 * n + 2) = (9 : Rat) / 32 := by
  rw [show 2 * n + 7 = 2 * n + 2 + 5 by omega]
  exact c11Cheap_ratio_K_inside_F (2 * n + 2)
theorem c11Cheap_H_tail_density
    (n : Nat) (lambda : C11CheapLowValuedWord) :
    c11CheapDyadicMass (2 * n + lambda.length + lambda.weight) +
        c11CheapDyadicMass (2 * n + lambda.length + lambda.weight + 1) =
      3 * c11CheapDyadicMass
        (2 * n + lambda.length + lambda.weight + 1) := by
  exact c11Cheap_dyadic_mass_add_next
    (2 * n + lambda.length + lambda.weight)
theorem c11Cheap_H_length_bank_density (n m : Nat) :
    c11CheapDyadicMass (2 * n) * ((3 : Rat) / 8) ^ m +
        c11CheapDyadicMass (2 * n + 1) * ((3 : Rat) / 8) ^ m =
      3 * c11CheapDyadicMass (2 * n + 1) * ((3 : Rat) / 8) ^ m := by
  rw [← add_mul]
  rw [c11Cheap_dyadic_mass_add_next (2 * n)]

def c11TPlusNumerator (n : Int) : Int := 3 * n + 1
def c11TMinusNumerator (q : Int) : Int := 3 * q - 1
def c11J (x : Int) : Int := -x
theorem c11_negation_numerator_identity (n : Int) :
    c11TMinusNumerator (c11J n) = -c11TPlusNumerator n := by
  unfold c11TMinusNumerator c11TPlusNumerator c11J
  omega
theorem c11_dvd_neg_iff (d x : Int) :
    d ∣ -x ↔ d ∣ x := by
  constructor
  · intro h
    rcases h with ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    calc
      x = -(d * k) := by omega
      _ = d * (-k) := by ring
  · intro h
    rcases h with ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    calc
      -x = -(d * k) := by omega
      _ = d * (-k) := by ring
theorem c11_negation_preserves_divisibility (d : Int) (n : Int) :
    d ∣ c11TMinusNumerator (c11J n) ↔ d ∣ c11TPlusNumerator n := by
  rw [c11_negation_numerator_identity n]
  exact c11_dvd_neg_iff d (c11TPlusNumerator n)
def c11ExactTwoValuation (x : Int) (k : Nat) : Prop :=
  (2 : Int) ^ k ∣ x ∧ ¬ (2 : Int) ^ (k + 1) ∣ x
theorem c11_exact_valuation_neg_iff (x : Int) (k : Nat) :
    c11ExactTwoValuation (-x) k ↔ c11ExactTwoValuation x k := by
  unfold c11ExactTwoValuation
  rw [c11_dvd_neg_iff ((2 : Int) ^ k) x,
    c11_dvd_neg_iff ((2 : Int) ^ (k + 1)) x]
def c11TPlusExactLayer (n : Int) (k : Nat) : Prop :=
  c11ExactTwoValuation (c11TPlusNumerator n) k
def c11TMinusExactLayer (q : Int) (k : Nat) : Prop :=
  c11ExactTwoValuation (c11TMinusNumerator q) k
theorem c11_exact_valuation_layer_bridge (n : Int) (k : Nat) :
    c11TMinusExactLayer (c11J n) k ↔ c11TPlusExactLayer n k := by
  unfold c11TMinusExactLayer c11TPlusExactLayer
  rw [c11_negation_numerator_identity n]
  exact c11_exact_valuation_neg_iff (c11TPlusNumerator n) k
theorem c11_divided_step_conjugacy
    (n n₁ : Int) (h : Nat)
    (hstep : c11TPlusNumerator n = (2 : Int) ^ h * n₁) :
    c11TMinusNumerator (c11J n) = (2 : Int) ^ h * c11J n₁ := by
  rw [c11_negation_numerator_identity, hstep]
  unfold c11J
  ring
structure C11TPlusStep (n n₁ : Int) (k : Nat) : Prop where
  exactLayer : c11TPlusExactLayer n k
  step : c11TPlusNumerator n = (2 : Int) ^ k * n₁
structure C11TMinusStep (q q₁ : Int) (k : Nat) : Prop where
  exactLayer : c11TMinusExactLayer q k
  step : c11TMinusNumerator q = (2 : Int) ^ k * q₁
theorem c11_tplus_step_to_tminus_step
    {n n₁ : Int} {k : Nat} (hstep : C11TPlusStep n n₁ k) :
    C11TMinusStep (c11J n) (c11J n₁) k where
  exactLayer := (c11_exact_valuation_layer_bridge n k).mpr hstep.exactLayer
  step := c11_divided_step_conjugacy n n₁ k hstep.step
def C11TPlusWordPath : List Nat → List Int → Prop
  | [], states => states.length = 1
  | k :: rest, n :: n₁ :: tail =>
      C11TPlusStep n n₁ k ∧ C11TPlusWordPath rest (n₁ :: tail)
  | _ :: _, _ => False
def C11TMinusWordPath : List Nat → List Int → Prop
  | [], states => states.length = 1
  | k :: rest, q :: q₁ :: tail =>
      C11TMinusStep q q₁ k ∧ C11TMinusWordPath rest (q₁ :: tail)
  | _ :: _, _ => False
def c11NegatePath (states : List Int) : List Int :=
  states.map c11J
theorem c11_finite_valuation_word_to_q_coordinate
    (word : List Nat) (states : List Int)
    (hpath : C11TPlusWordPath word states) :
    C11TMinusWordPath word (c11NegatePath states) := by
  induction word generalizing states with
  | nil =>
      unfold C11TPlusWordPath at hpath
      cases states with
      | nil =>
          simp at hpath
      | cons n rest =>
          cases rest with
          | nil =>
              simp [C11TMinusWordPath, c11NegatePath]
          | cons n₁ tail =>
              simp at hpath
  | cons k rest ih =>
      cases states with
      | nil =>
          simp [C11TPlusWordPath] at hpath
      | cons n statesTail =>
          cases statesTail with
          | nil =>
              simp [C11TPlusWordPath] at hpath
          | cons n₁ tail =>
              unfold C11TPlusWordPath at hpath
              rcases hpath with ⟨hstep, htail⟩
              unfold c11NegatePath C11TMinusWordPath
              exact ⟨c11_tplus_step_to_tminus_step hstep, ih (n₁ :: tail) htail⟩
theorem c11_residue_negation_bridge (M : Int) (n a : Int)
    (h : M ∣ n - a) :
    M ∣ c11J n - c11J a := by
  unfold c11J
  rcases h with ⟨k, hk⟩
  refine ⟨-k, ?_⟩
  calc
    -n - -a = -(n - a) := by ring
    _ = -(M * k) := by rw [hk]
    _ = M * (-k) := by ring
theorem c11_residue_negation_bridge_iff (M : Int) (n a : Int) :
    M ∣ c11J n - c11J a ↔ M ∣ n - a := by
  constructor
  · intro h
    have hback := c11_residue_negation_bridge M (c11J n) (c11J a) h
    simpa [c11J] using hback
  · exact c11_residue_negation_bridge M n a
theorem c11_post_break_plus_one_identity (n₁ : Int) :
    c11J n₁ + 1 = 1 - n₁ := by
  unfold c11J
  omega
theorem c11_post_break_deep_plus_one_collapses_to_first_layer
    (n₁ : Int)
    (hdeep : (4 : Int) ∣ n₁ + 1) :
    ∃ k : Int, c11J n₁ + 1 = 4 * k + 2 := by
  rcases hdeep with ⟨k, hk⟩
  refine ⟨-k, ?_⟩
  unfold c11J at *
  omega
structure C11QCoordinateNegationBridge : Prop where
  numerator_conjugacy :
    ∀ n : Int, c11TMinusNumerator (c11J n) = -c11TPlusNumerator n
  exact_layer_bridge :
    ∀ n : Int, ∀ k : Nat, c11TMinusExactLayer (c11J n) k ↔ c11TPlusExactLayer n k
  divided_step_conjugacy :
    ∀ n n₁ : Int, ∀ h : Nat,
      c11TPlusNumerator n = (2 : Int) ^ h * n₁ →
        c11TMinusNumerator (c11J n) = (2 : Int) ^ h * c11J n₁
  valuation_word_bridge :
    ∀ word states, C11TPlusWordPath word states →
      C11TMinusWordPath word (c11NegatePath states)
  residue_bridge :
    ∀ M n a : Int, M ∣ c11J n - c11J a ↔ M ∣ n - a
  post_break_plus_one :
    ∀ n₁ : Int, c11J n₁ + 1 = 1 - n₁
  deep_plus_one_collapse :
    ∀ n₁ : Int,
      (4 : Int) ∣ n₁ + 1 →
        ∃ k : Int, c11J n₁ + 1 = 4 * k + 2
theorem c11_q_coordinate_negation_bridge :
    C11QCoordinateNegationBridge where
  numerator_conjugacy := c11_negation_numerator_identity
  exact_layer_bridge := c11_exact_valuation_layer_bridge
  divided_step_conjugacy := c11_divided_step_conjugacy
  valuation_word_bridge := c11_finite_valuation_word_to_q_coordinate
  residue_bridge := c11_residue_negation_bridge_iff
  post_break_plus_one := c11_post_break_plus_one_identity
  deep_plus_one_collapse := c11_post_break_deep_plus_one_collapses_to_first_layer

noncomputable def c11DyadicMass (e : Nat) : Rat :=
  (1 : Rat) / (2 ^ e : Rat)
theorem c11_dyadic_mass_add_next (a : Nat) :
    c11DyadicMass a + c11DyadicMass (a + 1) =
      3 * c11DyadicMass (a + 1) := by
  unfold c11DyadicMass
  have hpow : (2 : Rat) ^ (a + 1) = (2 : Rat) ^ a * 2 := by
    rw [pow_add]
    norm_num
  rw [hpow]
  have hpos : (2 : Rat) ^ a ≠ 0 := pow_ne_zero a (by norm_num)
  field_simp [hpos]
  norm_num
theorem c11_dyadic_mass_mul (a b : Nat) :
    c11DyadicMass a * c11DyadicMass b = c11DyadicMass (a + b) := by
  unfold c11DyadicMass
  rw [pow_add]
  have ha : (2 : Rat) ^ a ≠ 0 := pow_ne_zero a (by norm_num)
  have hb : (2 : Rat) ^ b ≠ 0 := pow_ne_zero b (by norm_num)
  field_simp [ha, hb]
theorem c11_dyadic_mass_add_shift3 (a : Nat) :
    c11DyadicMass a + c11DyadicMass (a + 3) =
      9 * c11DyadicMass (a + 3) := by
  unfold c11DyadicMass
  have hpow : (2 : Rat) ^ (a + 3) = (2 : Rat) ^ a * 8 := by
    rw [pow_add]
    norm_num
  rw [hpow]
  have hpos : (2 : Rat) ^ a ≠ 0 := pow_ne_zero a (by norm_num)
  field_simp [hpos]
  norm_num
theorem c11_ratio_K_inside_F (a : Nat) :
    (9 * c11DyadicMass (a + 5)) / c11DyadicMass a = (9 : Rat) / 32 := by
  unfold c11DyadicMass
  have hpow : (2 : Rat) ^ (a + 5) = (2 : Rat) ^ a * 32 := by
    rw [pow_add]
    norm_num
  rw [hpow]
  have hpos : (2 : Rat) ^ a ≠ 0 := pow_ne_zero a (by norm_num)
  field_simp [hpos]
theorem c11_ratio_K_inside_H_lambda (a : Nat) :
    (9 * c11DyadicMass (a + 4)) / (3 * c11DyadicMass a) = (3 : Rat) / 16 := by
  unfold c11DyadicMass
  have hpow : (2 : Rat) ^ (a + 4) = (2 : Rat) ^ a * 16 := by
    rw [pow_add]
    norm_num
  rw [hpow]
  have hpos : (2 : Rat) ^ a ≠ 0 := pow_ne_zero a (by norm_num)
  field_simp [hpos]
  norm_num
theorem c11_ratio_K_inside_H_one_word_bank (a : Nat) :
    (9 * c11DyadicMass (a + 3)) / (9 * c11DyadicMass a) = (1 : Rat) / 8 := by
  unfold c11DyadicMass
  have hpow : (2 : Rat) ^ (a + 3) = (2 : Rat) ^ a * 8 := by
    rw [pow_add]
    norm_num
  rw [hpow]
  have hpos : (2 : Rat) ^ a ≠ 0 := pow_ne_zero a (by norm_num)
  field_simp [hpos]
theorem c11_low_valued_letter_mass_sum :
    c11DyadicMass 2 + c11DyadicMass 3 = (3 : Rat) / 8 := by
  unfold c11DyadicMass
  norm_num
noncomputable def c11LowValuedWordMassSum : Nat → Rat
  | 0 => 1
  | m + 1 => c11LowValuedWordMassSum m * (c11DyadicMass 2 + c11DyadicMass 3)
theorem c11_low_valued_word_mass_sum_formula (m : Nat) :
    c11LowValuedWordMassSum m = ((3 : Rat) / 8) ^ m := by
  induction m with
  | zero =>
      simp [c11LowValuedWordMassSum]
  | succ m ih =>
      simp [c11LowValuedWordMassSum, ih, c11_low_valued_letter_mass_sum,
        pow_succ, mul_comm]
theorem c11_H_m_relative_density_formula (n m : Nat) :
    3 * c11DyadicMass (2 * n + 1) * c11LowValuedWordMassSum m =
      3 * c11DyadicMass (2 * n + 1) * ((3 : Rat) / 8) ^ m := by
  rw [c11_low_valued_word_mass_sum_formula]
theorem c11_H_m_absolute_density_formula (Tau n m : Nat) :
    c11DyadicMass Tau *
        (3 * c11DyadicMass (2 * n + 1) * ((3 : Rat) / 8) ^ m) =
      3 * c11DyadicMass (Tau + 2 * n + 1) * ((3 : Rat) / 8) ^ m := by
  calc
    c11DyadicMass Tau *
        (3 * c11DyadicMass (2 * n + 1) * ((3 : Rat) / 8) ^ m)
        = 3 * (c11DyadicMass Tau * c11DyadicMass (2 * n + 1)) *
            ((3 : Rat) / 8) ^ m := by ring
    _ = 3 * c11DyadicMass (Tau + (2 * n + 1)) *
            ((3 : Rat) / 8) ^ m := by
          rw [c11_dyadic_mass_mul]
    _ = 3 * c11DyadicMass (Tau + 2 * n + 1) *
            ((3 : Rat) / 8) ^ m := by
          rw [show Tau + (2 * n + 1) = Tau + 2 * n + 1 by omega]
def c11SetPullback {α β : Type} (Q : α → β) (A : Set β) : Set α :=
  {x | Q x ∈ A}
theorem c11_set_pullback_subset {α β : Type} (Q : α → β)
    {A B : Set β} (hAB : A ⊆ B) :
    c11SetPullback Q A ⊆ c11SetPullback Q B := by
  intro x hx
  exact hAB hx
theorem c11_set_pullback_union {α β : Type} (Q : α → β)
    (A B : Set β) :
    c11SetPullback Q (A ∪ B) =
      c11SetPullback Q A ∪ c11SetPullback Q B := by
  ext x
  rfl
def c11SetDisjoint {α : Type} (A B : Set α) : Prop :=
  ∀ x, x ∈ A → x ∈ B → False
theorem c11_set_pullback_disjoint {α β : Type} (Q : α → β)
    {A B : Set β} (hAB : c11SetDisjoint A B) :
    c11SetDisjoint (c11SetPullback Q A) (c11SetPullback Q B) := by
  intro x hxA hxB
  exact hAB (Q x) hxA hxB
theorem c11_set_pullback_pairwise_disjoint {α β ι : Type} (Q : α → β)
    (A : ι → Set β)
    (hpair : ∀ i j, i ≠ j → c11SetDisjoint (A i) (A j)) :
    ∀ i j, i ≠ j →
      c11SetDisjoint (c11SetPullback Q (A i)) (c11SetPullback Q (A j)) := by
  intro i j hij
  exact c11_set_pullback_disjoint Q (hpair i j hij)
theorem c11_set_pullback_biUnion {α β ι : Type} [DecidableEq ι]
    (Q : α → β) (s : Finset ι) (A : ι → Set β) :
    c11SetPullback Q (⋃ i ∈ s, A i) =
      ⋃ i ∈ s, c11SetPullback Q (A i) := by
  ext x
  simp [c11SetPullback]
structure C11OneOddResidueClass where
  exponent : Nat
  residue : Nat
  residue_odd : residue % 2 = 1
structure C11TerminalFreeExactPathFamily where
  Tau : Nat
  Y : C11OneOddResidueClass
  Y_exponent : Y.exponent = Tau + 1
  Y_density : Rat
  Y_density_eq : Y_density = c11DyadicMass Tau
  pullbackClass : C11OneOddResidueClass → C11OneOddResidueClass
  pullback_exponent :
    ∀ terminalClass, (pullbackClass terminalClass).exponent =
      Tau + terminalClass.exponent
  pullback_absolute_density : C11OneOddResidueClass → Rat
  pullback_absolute_density_eq :
    ∀ terminalClass, pullback_absolute_density terminalClass =
      c11DyadicMass (Tau + terminalClass.exponent - 1)
  pullback_relative_density : C11OneOddResidueClass → Rat
  pullback_relative_density_eq :
    ∀ terminalClass, pullback_relative_density terminalClass =
      c11DyadicMass (terminalClass.exponent - 1)
theorem c11_exact_path_pullback_class
    (Y : C11TerminalFreeExactPathFamily) (terminalClass : C11OneOddResidueClass) :
    (Y.pullbackClass terminalClass).exponent = Y.Tau + terminalClass.exponent ∧
      Y.pullback_absolute_density terminalClass =
        c11DyadicMass (Y.Tau + terminalClass.exponent - 1) ∧
      Y.pullback_relative_density terminalClass =
        c11DyadicMass (terminalClass.exponent - 1) := by
  exact ⟨Y.pullback_exponent terminalClass,
    Y.pullback_absolute_density_eq terminalClass,
    Y.pullback_relative_density_eq terminalClass⟩
structure C11LowValuedWord where
  entries : List Nat
  entries_one_or_two : ∀ ell ∈ entries, ell = 1 ∨ ell = 2
namespace C11LowValuedWord
def length (lambda : C11LowValuedWord) : Nat :=
  lambda.entries.length
def weight (lambda : C11LowValuedWord) : Nat :=
  lambda.entries.sum
end C11LowValuedWord
structure C11CheapChainTerminalClasses (n : Nat) (lambda : C11LowValuedWord) where
  F : C11OneOddResidueClass
  F_exponent :
    F.exponent = 2 * n + lambda.length + lambda.weight + 1
  G : C11OneOddResidueClass
  G_exponent :
    G.exponent = 2 * n + lambda.length + lambda.weight + 2
  disjoint_FG : Prop
def c11FExponent (n : Nat) (lambda : C11LowValuedWord) : Nat :=
  2 * n + lambda.length + lambda.weight + 1
def c11GExponent (n : Nat) (lambda : C11LowValuedWord) : Nat :=
  2 * n + lambda.length + lambda.weight + 2
def c11FRelativeExponent (n : Nat) (lambda : C11LowValuedWord) : Nat :=
  2 * n + lambda.length + lambda.weight
def c11GRelativeExponent (n : Nat) (lambda : C11LowValuedWord) : Nat :=
  2 * n + lambda.length + lambda.weight + 1
theorem c11_H_lambda_relative_density_formula
    (n : Nat) (lambda : C11LowValuedWord) :
    c11DyadicMass (c11FRelativeExponent n lambda) +
        c11DyadicMass (c11GRelativeExponent n lambda) =
      3 * c11DyadicMass (2 * n + lambda.length + lambda.weight + 1) := by
  unfold c11FRelativeExponent c11GRelativeExponent
  exact c11_dyadic_mass_add_next (2 * n + lambda.length + lambda.weight)
structure C11LowValuedEntryBankPullback
    (Y : C11TerminalFreeExactPathFamily) (n : Nat) (lambda : C11LowValuedWord)
    where
  terminal : C11CheapChainTerminalClasses n lambda
  FY : C11OneOddResidueClass
  FY_eq_pullback : FY = Y.pullbackClass terminal.F
  FY_exponent :
    FY.exponent = Y.Tau + 2 * n + lambda.length + lambda.weight + 1
  FY_relative_density : Rat
  FY_relative_density_eq :
    FY_relative_density =
      c11DyadicMass (2 * n + lambda.length + lambda.weight)
  GY : C11OneOddResidueClass
  GY_eq_pullback : GY = Y.pullbackClass terminal.G
  GY_exponent :
    GY.exponent = Y.Tau + 2 * n + lambda.length + lambda.weight + 2
  GY_relative_density : Rat
  GY_relative_density_eq :
    GY_relative_density =
      c11DyadicMass (2 * n + lambda.length + lambda.weight + 1)
  H_relative_density : Rat
  H_relative_density_eq :
    H_relative_density =
      3 * c11DyadicMass (2 * n + lambda.length + lambda.weight + 1)
  FG_disjoint : terminal.disjoint_FG
structure C11LowValuedLengthBankTerminal (n m : Nat) where
  words : Finset C11LowValuedWord
  all_length_m : ∀ lambda ∈ words, lambda.length = m
  pairwise_disjoint_terminal : Prop
  terminal_mass_sum :
    c11LowValuedWordMassSum m = ((3 : Rat) / 8) ^ m
structure C11LowValuedLengthBankPullback
    (Y : C11TerminalFreeExactPathFamily) (n m : Nat) where
  terminal : C11LowValuedLengthBankTerminal n m
  pairwise_disjoint_pulled_back : Prop
  H_m_relative_density : Rat
  H_m_relative_density_eq :
    H_m_relative_density =
      3 * c11DyadicMass (2 * n + 1) * ((3 : Rat) / 8) ^ m
  H_m_absolute_density : Rat
  H_m_absolute_density_eq :
    H_m_absolute_density =
      3 * c11DyadicMass (Y.Tau + 2 * n + 1) * ((3 : Rat) / 8) ^ m
noncomputable def c11_terminal_free_exact_path_low_valued_length_bank
    (Y : C11TerminalFreeExactPathFamily) (n m : Nat)
    (terminal : C11LowValuedLengthBankTerminal n m)
    (hpullback_disjoint : Prop) :
    C11LowValuedLengthBankPullback Y n m := by
  refine
    { terminal := terminal
      pairwise_disjoint_pulled_back := hpullback_disjoint
      H_m_relative_density :=
        3 * c11DyadicMass (2 * n + 1) * c11LowValuedWordMassSum m
      H_m_relative_density_eq := ?_
      H_m_absolute_density :=
        c11DyadicMass Y.Tau *
          (3 * c11DyadicMass (2 * n + 1) * ((3 : Rat) / 8) ^ m)
      H_m_absolute_density_eq := ?_ }
  · exact c11_H_m_relative_density_formula n m
  · exact c11_H_m_absolute_density_formula Y.Tau n m
def c11_terminal_free_exact_path_low_valued_entry_bank
    (Y : C11TerminalFreeExactPathFamily) (n : Nat) (lambda : C11LowValuedWord)
    (terminal : C11CheapChainTerminalClasses n lambda)
    (hdisjoint : terminal.disjoint_FG) :
    C11LowValuedEntryBankPullback Y n lambda := by
  refine
    { terminal := terminal
      FY := Y.pullbackClass terminal.F
      FY_eq_pullback := rfl
      FY_exponent := ?_
      FY_relative_density := Y.pullback_relative_density terminal.F
      FY_relative_density_eq := ?_
      GY := Y.pullbackClass terminal.G
      GY_eq_pullback := rfl
      GY_exponent := ?_
      GY_relative_density := Y.pullback_relative_density terminal.G
      GY_relative_density_eq := ?_
      H_relative_density :=
        Y.pullback_relative_density terminal.F +
          Y.pullback_relative_density terminal.G
      H_relative_density_eq := ?_
      FG_disjoint := hdisjoint }
  · rw [Y.pullback_exponent terminal.F, terminal.F_exponent]
    omega
  · rw [Y.pullback_relative_density_eq terminal.F, terminal.F_exponent]
    have hidx :
        2 * n + lambda.length + lambda.weight + 1 - 1 =
          2 * n + lambda.length + lambda.weight := by omega
    rw [hidx]
  · rw [Y.pullback_exponent terminal.G, terminal.G_exponent]
    omega
  · rw [Y.pullback_relative_density_eq terminal.G, terminal.G_exponent]
    have hidx :
        2 * n + lambda.length + lambda.weight + 2 - 1 =
          2 * n + lambda.length + lambda.weight + 1 := by omega
    rw [hidx]
  · rw [Y.pullback_relative_density_eq terminal.F,
      Y.pullback_relative_density_eq terminal.G,
      terminal.F_exponent, terminal.G_exponent]
    have hF :
        2 * n + lambda.length + lambda.weight + 1 - 1 =
          2 * n + lambda.length + lambda.weight := by omega
    have hG :
        2 * n + lambda.length + lambda.weight + 2 - 1 =
          2 * n + lambda.length + lambda.weight + 1 := by omega
    rw [hF, hG]
    exact c11_H_lambda_relative_density_formula n lambda
structure C11K1TerminalNegativeGapBank (n : Nat) where
  A : C11OneOddResidueClass
  A_exponent : A.exponent = 2 * n + 5
  B : C11OneOddResidueClass
  B_exponent : B.exponent = 2 * n + 8
  disjoint_AB : Prop
  negative_gap : Prop
structure C11K1NegativeGapPullback
    (Y : C11TerminalFreeExactPathFamily) (n : Nat) where
  terminal : C11K1TerminalNegativeGapBank n
  AY : C11OneOddResidueClass
  AY_eq_pullback : AY = Y.pullbackClass terminal.A
  AY_exponent : AY.exponent = Y.Tau + 2 * n + 5
  AY_relative_density : Rat
  AY_relative_density_eq : AY_relative_density = c11DyadicMass (2 * n + 4)
  BY : C11OneOddResidueClass
  BY_eq_pullback : BY = Y.pullbackClass terminal.B
  BY_exponent : BY.exponent = Y.Tau + 2 * n + 8
  BY_relative_density : Rat
  BY_relative_density_eq : BY_relative_density = c11DyadicMass (2 * n + 7)
  K_relative_density : Rat
  K_relative_density_eq : K_relative_density = 9 * c11DyadicMass (2 * n + 7)
  K_absolute_density : Rat
  K_absolute_density_eq : K_absolute_density = 9 * c11DyadicMass (Y.Tau + 2 * n + 7)
  AB_disjoint : terminal.disjoint_AB
  negative_gap : terminal.negative_gap
def c11_terminal_free_exact_path_negative_gap_K1
    (Y : C11TerminalFreeExactPathFamily) (n : Nat)
    (terminal : C11K1TerminalNegativeGapBank n)
    (hdisjoint : terminal.disjoint_AB)
    (hgap : terminal.negative_gap) :
    C11K1NegativeGapPullback Y n := by
  refine
    { terminal := terminal
      AY := Y.pullbackClass terminal.A
      AY_eq_pullback := rfl
      AY_exponent := ?_
      AY_relative_density := Y.pullback_relative_density terminal.A
      AY_relative_density_eq := ?_
      BY := Y.pullbackClass terminal.B
      BY_eq_pullback := rfl
      BY_exponent := ?_
      BY_relative_density := Y.pullback_relative_density terminal.B
      BY_relative_density_eq := ?_
      K_relative_density :=
        Y.pullback_relative_density terminal.A +
          Y.pullback_relative_density terminal.B
      K_relative_density_eq := ?_
      K_absolute_density :=
        Y.Y_density *
          (Y.pullback_relative_density terminal.A +
            Y.pullback_relative_density terminal.B)
      K_absolute_density_eq := ?_
      AB_disjoint := hdisjoint
      negative_gap := hgap }
  · rw [Y.pullback_exponent terminal.A, terminal.A_exponent]
    omega
  · rw [Y.pullback_relative_density_eq terminal.A, terminal.A_exponent]
    have hidx : 2 * n + 5 - 1 = 2 * n + 4 := by omega
    rw [hidx]
  · rw [Y.pullback_exponent terminal.B, terminal.B_exponent]
    omega
  · rw [Y.pullback_relative_density_eq terminal.B, terminal.B_exponent]
    have hidx : 2 * n + 8 - 1 = 2 * n + 7 := by omega
    rw [hidx]
  · rw [Y.pullback_relative_density_eq terminal.A,
      Y.pullback_relative_density_eq terminal.B,
      terminal.A_exponent, terminal.B_exponent]
    have hA : 2 * n + 5 - 1 = 2 * n + 4 := by omega
    have hB : 2 * n + 8 - 1 = 2 * n + 7 := by omega
    rw [hA, hB]
    exact c11_dyadic_mass_add_shift3 (2 * n + 4)
  · rw [Y.Y_density_eq,
      Y.pullback_relative_density_eq terminal.A,
      Y.pullback_relative_density_eq terminal.B,
      terminal.A_exponent, terminal.B_exponent]
    have hA : 2 * n + 5 - 1 = 2 * n + 4 := by omega
    have hB : 2 * n + 8 - 1 = 2 * n + 7 := by omega
    rw [hA, hB, c11_dyadic_mass_add_shift3 (2 * n + 4)]
    rw [show c11DyadicMass Y.Tau * (9 * c11DyadicMass (2 * n + 4 + 3)) =
      9 * (c11DyadicMass Y.Tau * c11DyadicMass (2 * n + 4 + 3)) by ring]
    rw [c11_dyadic_mass_mul]
    have hidx : Y.Tau + (2 * n + 7) = Y.Tau + 2 * n + 7 := by omega
    rw [hidx]
structure C11ExactWord22Terminal where
  E22 : C11OneOddResidueClass
  E22_exponent : E22.exponent = 7
structure C11ExactWord22Pullback
    (Y : C11TerminalFreeExactPathFamily) where
  terminal : C11ExactWord22Terminal
  WY : C11OneOddResidueClass
  WY_eq_pullback : WY = Y.pullbackClass terminal.E22
  WY_exponent : WY.exponent = Y.Tau + 7
  WY_relative_density : Rat
  WY_relative_density_eq : WY_relative_density = (1 : Rat) / 64
  WY_absolute_density : Rat
  WY_absolute_density_eq : WY_absolute_density = c11DyadicMass (Y.Tau + 6)
def c11_terminal_free_exact_path_word22_pullback
    (Y : C11TerminalFreeExactPathFamily)
    (terminal : C11ExactWord22Terminal) :
    C11ExactWord22Pullback Y := by
  refine
    { terminal := terminal
      WY := Y.pullbackClass terminal.E22
      WY_eq_pullback := rfl
      WY_exponent := ?_
      WY_relative_density := Y.pullback_relative_density terminal.E22
      WY_relative_density_eq := ?_
      WY_absolute_density := Y.pullback_absolute_density terminal.E22
      WY_absolute_density_eq := ?_ }
  · rw [Y.pullback_exponent terminal.E22, terminal.E22_exponent]
  · rw [Y.pullback_relative_density_eq terminal.E22, terminal.E22_exponent]
    norm_num [c11DyadicMass]
  · rw [Y.pullback_absolute_density_eq terminal.E22, terminal.E22_exponent]
    have hidx : Y.Tau + 7 - 1 = Y.Tau + 6 := by omega
    rw [hidx]
theorem c11_K1_mass_ratio_inside_F_one
    (n : Nat) :
    (9 * c11DyadicMass (2 * n + 7)) /
        c11DyadicMass (2 * n + 2) = (9 : Rat) / 32 := by
  have hidx : 2 * n + 7 = (2 * n + 2) + 5 := by omega
  rw [hidx]
  exact c11_ratio_K_inside_F (2 * n + 2)
theorem c11_K1_mass_ratio_inside_H_single_lambda
    (n : Nat) :
    (9 * c11DyadicMass (2 * n + 7)) /
        (3 * c11DyadicMass (2 * n + 3)) = (3 : Rat) / 16 := by
  have hidx : 2 * n + 7 = (2 * n + 3) + 4 := by omega
  rw [hidx]
  exact c11_ratio_K_inside_H_lambda (2 * n + 3)
theorem c11_K1_mass_ratio_inside_H_one_word_bank
    (n : Nat) :
    (9 * c11DyadicMass (2 * n + 7)) /
        (9 * c11DyadicMass (2 * n + 4)) = (1 : Rat) / 8 := by
  have hidx : 2 * n + 7 = (2 * n + 4) + 3 := by omega
  rw [hidx]
  exact c11_ratio_K_inside_H_one_word_bank (2 * n + 4)
def c11WordOne : C11LowValuedWord where
  entries := [1]
  entries_one_or_two := by
    intro ell hell
    simp at hell
    exact Or.inl hell
theorem c11WordOne_length : c11WordOne.length = 1 := by rfl
theorem c11WordOne_weight : c11WordOne.weight = 1 := by rfl
structure C11K1InsideFOne
    (Y : C11TerminalFreeExactPathFamily) (n : Nat) where
  low : C11LowValuedEntryBankPullback Y n c11WordOne
  kbank : C11K1NegativeGapPullback Y n
  subset_terminal : Prop
  subset_pulled_back : Prop
  F_density : Rat
  F_density_eq : F_density = c11DyadicMass (2 * n + 2)
  K_density : Rat
  K_density_eq : K_density = 9 * c11DyadicMass (2 * n + 7)
  K_inside_F_ratio : K_density / F_density = (9 : Rat) / 32
def c11_K1_inside_F_one
    (Y : C11TerminalFreeExactPathFamily) (n : Nat)
    (low : C11LowValuedEntryBankPullback Y n c11WordOne)
    (kbank : C11K1NegativeGapPullback Y n)
    (hsubset_terminal : Prop)
    (hsubset_pulled_back : Prop) :
    C11K1InsideFOne Y n := by
  refine
    { low := low
      kbank := kbank
      subset_terminal := hsubset_terminal
      subset_pulled_back := hsubset_pulled_back
      F_density := low.FY_relative_density
      F_density_eq := ?_
      K_density := kbank.K_relative_density
      K_density_eq := kbank.K_relative_density_eq
      K_inside_F_ratio := ?_ }
  · rw [low.FY_relative_density_eq, c11WordOne_length, c11WordOne_weight]
  · rw [low.FY_relative_density_eq, kbank.K_relative_density_eq,
      c11WordOne_length, c11WordOne_weight]
    exact c11_K1_mass_ratio_inside_F_one n
structure C11K1InsideHSingleLambda
    (Y : C11TerminalFreeExactPathFamily) (n : Nat) where
  low : C11LowValuedEntryBankPullback Y n c11WordOne
  kbank : C11K1NegativeGapPullback Y n
  subset_pulled_back : Prop
  H_density : Rat
  H_density_eq : H_density = 3 * c11DyadicMass (2 * n + 3)
  K_density : Rat
  K_density_eq : K_density = 9 * c11DyadicMass (2 * n + 7)
  K_inside_H_ratio : K_density / H_density = (3 : Rat) / 16
def c11_K1_inside_H_single_lambda
    (Y : C11TerminalFreeExactPathFamily) (n : Nat)
    (low : C11LowValuedEntryBankPullback Y n c11WordOne)
    (kbank : C11K1NegativeGapPullback Y n)
    (hsubset_pulled_back : Prop) :
    C11K1InsideHSingleLambda Y n := by
  refine
    { low := low
      kbank := kbank
      subset_pulled_back := hsubset_pulled_back
      H_density := low.H_relative_density
      H_density_eq := ?_
      K_density := kbank.K_relative_density
      K_density_eq := kbank.K_relative_density_eq
      K_inside_H_ratio := ?_ }
  · rw [low.H_relative_density_eq, c11WordOne_length, c11WordOne_weight]
  · rw [low.H_relative_density_eq, kbank.K_relative_density_eq,
      c11WordOne_length, c11WordOne_weight]
    exact c11_K1_mass_ratio_inside_H_single_lambda n
structure C11K1InsideHOneWordBank
    (Y : C11TerminalFreeExactPathFamily) (n : Nat) where
  kbank : C11K1NegativeGapPullback Y n
  subset_pulled_back : Prop
  H_one_word_density : Rat
  H_one_word_density_eq : H_one_word_density = 9 * c11DyadicMass (2 * n + 4)
  K_density : Rat
  K_density_eq : K_density = 9 * c11DyadicMass (2 * n + 7)
  K_inside_H_one_word_ratio : K_density / H_one_word_density = (1 : Rat) / 8
noncomputable def c11_K1_inside_H_one_word_bank
    (Y : C11TerminalFreeExactPathFamily) (n : Nat)
    (kbank : C11K1NegativeGapPullback Y n)
    (hsubset_pulled_back : Prop) :
    C11K1InsideHOneWordBank Y n := by
  refine
    { kbank := kbank
      subset_pulled_back := hsubset_pulled_back
      H_one_word_density := 9 * c11DyadicMass (2 * n + 4)
      H_one_word_density_eq := rfl
      K_density := kbank.K_relative_density
      K_density_eq := kbank.K_relative_density_eq
      K_inside_H_one_word_ratio := ?_ }
  rw [kbank.K_relative_density_eq]
  exact c11_K1_mass_ratio_inside_H_one_word_bank n
structure C11CheapEscapeTerminalBranch (n : Nat) where
  Bge3 : C11OneOddResidueClass
  Bge3_exponent : Bge3.exponent = 2 * n + 2
  cheap_escape : Prop
  negative_gap : Prop
structure C11CheapEscapePullback
    (Y : C11TerminalFreeExactPathFamily) (n : Nat) where
  terminal : C11CheapEscapeTerminalBranch n
  EY : C11OneOddResidueClass
  EY_eq_pullback : EY = Y.pullbackClass terminal.Bge3
  EY_exponent : EY.exponent = Y.Tau + 2 * n + 2
  EY_relative_density : Rat
  EY_relative_density_eq : EY_relative_density = c11DyadicMass (2 * n + 1)
  EY_absolute_density : Rat
  EY_absolute_density_eq : EY_absolute_density = c11DyadicMass (Y.Tau + 2 * n + 1)
  cheap_escape : terminal.cheap_escape
  negative_gap : terminal.negative_gap
def c11_terminal_free_exact_path_cheap_escape_branch
    (Y : C11TerminalFreeExactPathFamily) (n : Nat)
    (terminal : C11CheapEscapeTerminalBranch n)
    (hcheap : terminal.cheap_escape)
    (hgap : terminal.negative_gap) :
    C11CheapEscapePullback Y n := by
  refine
    { terminal := terminal
      EY := Y.pullbackClass terminal.Bge3
      EY_eq_pullback := rfl
      EY_exponent := ?_
      EY_relative_density := Y.pullback_relative_density terminal.Bge3
      EY_relative_density_eq := ?_
      EY_absolute_density := Y.pullback_absolute_density terminal.Bge3
      EY_absolute_density_eq := ?_
      cheap_escape := hcheap
      negative_gap := hgap }
  · rw [Y.pullback_exponent terminal.Bge3, terminal.Bge3_exponent]
    omega
  · rw [Y.pullback_relative_density_eq terminal.Bge3, terminal.Bge3_exponent]
    have hidx : 2 * n + 2 - 1 = 2 * n + 1 := by omega
    rw [hidx]
  · rw [Y.pullback_absolute_density_eq terminal.Bge3, terminal.Bge3_exponent]
    have hidx : Y.Tau + (2 * n + 2) - 1 = Y.Tau + 2 * n + 1 := by omega
    rw [hidx]
structure C11TerminalClass21 where
  C21 : C11OneOddResidueClass
  C21_exponent : C21.exponent = 6
  valuation_two : Prop
  next_length_one : Prop
  next_residue_9_mod16 : Prop
  negative_gap : Prop
structure C11Class21Pullback
    (Y : C11TerminalFreeExactPathFamily) where
  terminal : C11TerminalClass21
  NY : C11OneOddResidueClass
  NY_eq_pullback : NY = Y.pullbackClass terminal.C21
  NY_exponent : NY.exponent = Y.Tau + 6
  NY_relative_density : Rat
  NY_relative_density_eq : NY_relative_density = (1 : Rat) / 32
  NY_absolute_density : Rat
  NY_absolute_density_eq : NY_absolute_density = c11DyadicMass (Y.Tau + 5)
  valuation_two : terminal.valuation_two
  next_length_one : terminal.next_length_one
  next_residue_9_mod16 : terminal.next_residue_9_mod16
  negative_gap : terminal.negative_gap
def c11_terminal_free_exact_path_class21_pullback
    (Y : C11TerminalFreeExactPathFamily)
    (terminal : C11TerminalClass21)
    (hval : terminal.valuation_two)
    (hlen : terminal.next_length_one)
    (hres : terminal.next_residue_9_mod16)
    (hgap : terminal.negative_gap) :
    C11Class21Pullback Y := by
  refine
    { terminal := terminal
      NY := Y.pullbackClass terminal.C21
      NY_eq_pullback := rfl
      NY_exponent := ?_
      NY_relative_density := Y.pullback_relative_density terminal.C21
      NY_relative_density_eq := ?_
      NY_absolute_density := Y.pullback_absolute_density terminal.C21
      NY_absolute_density_eq := ?_
      valuation_two := hval
      next_length_one := hlen
      next_residue_9_mod16 := hres
      negative_gap := hgap }
  · rw [Y.pullback_exponent terminal.C21, terminal.C21_exponent]
  · rw [Y.pullback_relative_density_eq terminal.C21, terminal.C21_exponent]
    norm_num [c11DyadicMass]
  · rw [Y.pullback_absolute_density_eq terminal.C21, terminal.C21_exponent]
    have hidx : Y.Tau + 6 - 1 = Y.Tau + 5 := by omega
    rw [hidx]
structure C11TerminalBranch11Bank where
  N9 : C11OneOddResidueClass
  N9_exponent : N9.exponent = 5
  N13 : C11OneOddResidueClass
  N13_exponent : N13.exponent = 8
  disjoint_N9_N13 : Prop
  exact_branch_111 : Prop
  negative_gap : Prop
structure C11Branch11Pullback
    (Y : C11TerminalFreeExactPathFamily) where
  terminal : C11TerminalBranch11Bank
  N9Y : C11OneOddResidueClass
  N9Y_eq_pullback : N9Y = Y.pullbackClass terminal.N9
  N9Y_exponent : N9Y.exponent = Y.Tau + 5
  N9Y_relative_density : Rat
  N9Y_relative_density_eq : N9Y_relative_density = (1 : Rat) / 16
  N13Y : C11OneOddResidueClass
  N13Y_eq_pullback : N13Y = Y.pullbackClass terminal.N13
  N13Y_exponent : N13Y.exponent = Y.Tau + 8
  N13Y_relative_density : Rat
  N13Y_relative_density_eq : N13Y_relative_density = (1 : Rat) / 128
  BY_relative_density : Rat
  BY_relative_density_eq : BY_relative_density = (9 : Rat) / 128
  BY_absolute_density : Rat
  BY_absolute_density_eq : BY_absolute_density = 9 * c11DyadicMass (Y.Tau + 7)
  disjoint : terminal.disjoint_N9_N13
  exact_branch_111 : terminal.exact_branch_111
  negative_gap : terminal.negative_gap
def c11_terminal_free_exact_path_branch11_pullback
    (Y : C11TerminalFreeExactPathFamily)
    (terminal : C11TerminalBranch11Bank)
    (hdisjoint : terminal.disjoint_N9_N13)
    (hbranch : terminal.exact_branch_111)
    (hgap : terminal.negative_gap) :
    C11Branch11Pullback Y := by
  refine
    { terminal := terminal
      N9Y := Y.pullbackClass terminal.N9
      N9Y_eq_pullback := rfl
      N9Y_exponent := ?_
      N9Y_relative_density := Y.pullback_relative_density terminal.N9
      N9Y_relative_density_eq := ?_
      N13Y := Y.pullbackClass terminal.N13
      N13Y_eq_pullback := rfl
      N13Y_exponent := ?_
      N13Y_relative_density := Y.pullback_relative_density terminal.N13
      N13Y_relative_density_eq := ?_
      BY_relative_density :=
        Y.pullback_relative_density terminal.N9 +
          Y.pullback_relative_density terminal.N13
      BY_relative_density_eq := ?_
      BY_absolute_density :=
        Y.Y_density *
          (Y.pullback_relative_density terminal.N9 +
            Y.pullback_relative_density terminal.N13)
      BY_absolute_density_eq := ?_
      disjoint := hdisjoint
      exact_branch_111 := hbranch
      negative_gap := hgap }
  · rw [Y.pullback_exponent terminal.N9, terminal.N9_exponent]
  · rw [Y.pullback_relative_density_eq terminal.N9, terminal.N9_exponent]
    norm_num [c11DyadicMass]
  · rw [Y.pullback_exponent terminal.N13, terminal.N13_exponent]
  · rw [Y.pullback_relative_density_eq terminal.N13, terminal.N13_exponent]
    norm_num [c11DyadicMass]
  · rw [Y.pullback_relative_density_eq terminal.N9,
      Y.pullback_relative_density_eq terminal.N13,
      terminal.N9_exponent, terminal.N13_exponent]
    norm_num [c11DyadicMass]
  · rw [Y.Y_density_eq,
      Y.pullback_relative_density_eq terminal.N9,
      Y.pullback_relative_density_eq terminal.N13,
      terminal.N9_exponent, terminal.N13_exponent]
    norm_num [c11DyadicMass]
    have hpow : (2 : Rat) ^ (Y.Tau + 7) = (2 : Rat) ^ Y.Tau * 128 := by
      rw [pow_add]
      norm_num
    rw [hpow]
    have hpos : (2 : Rat) ^ Y.Tau ≠ 0 := pow_ne_zero Y.Tau (by norm_num)
    field_simp [hpos]
theorem c11_two_piece_atlas_relative_density :
    (9 : Rat) / 128 + (1 : Rat) / 32 = (13 : Rat) / 128 := by
  norm_num
theorem c11_two_piece_atlas_absolute_density (Tau : Nat) :
    ((13 : Rat) / 128) * c11DyadicMass Tau =
      13 * c11DyadicMass (Tau + 7) := by
  unfold c11DyadicMass
  have hpow : (2 : Rat) ^ (Tau + 7) = (2 : Rat) ^ Tau * 128 := by
    rw [pow_add]
    norm_num
  rw [hpow]
  have hpos : (2 : Rat) ^ Tau ≠ 0 := pow_ne_zero Tau (by norm_num)
  field_simp [hpos]
structure C11TwoPieceLowValuedObstructionAtlas
    (Y : C11TerminalFreeExactPathFamily) where
  branch11 : C11Branch11Pullback Y
  class21 : C11Class21Pullback Y
  disjoint_branch11_class21 : Prop
  atlas_relative_density : Rat
  atlas_relative_density_eq : atlas_relative_density = (13 : Rat) / 128
  atlas_absolute_density : Rat
  atlas_absolute_density_eq :
    atlas_absolute_density = 13 * c11DyadicMass (Y.Tau + 7)
  branch11_negative_gap : Prop
  class21_negative_gap : Prop
def c11_two_piece_low_valued_obstruction_atlas
    (Y : C11TerminalFreeExactPathFamily)
    (branch11 : C11Branch11Pullback Y)
    (class21 : C11Class21Pullback Y)
    (hdisjoint : Prop)
    (hgap11 : Prop)
    (hgap21 : Prop) :
    C11TwoPieceLowValuedObstructionAtlas Y := by
  refine
    { branch11 := branch11
      class21 := class21
      disjoint_branch11_class21 := hdisjoint
      atlas_relative_density :=
        branch11.BY_relative_density + class21.NY_relative_density
      atlas_relative_density_eq := ?_
      atlas_absolute_density :=
        Y.Y_density *
          (branch11.BY_relative_density + class21.NY_relative_density)
      atlas_absolute_density_eq := ?_
      branch11_negative_gap := hgap11
      class21_negative_gap := hgap21 }
  · rw [branch11.BY_relative_density_eq, class21.NY_relative_density_eq]
    exact c11_two_piece_atlas_relative_density
  · rw [Y.Y_density_eq, branch11.BY_relative_density_eq,
      class21.NY_relative_density_eq, c11_two_piece_atlas_relative_density]
    rw [show c11DyadicMass Y.Tau * ((13 : Rat) / 128) =
      ((13 : Rat) / 128) * c11DyadicMass Y.Tau by ring]
    exact c11_two_piece_atlas_absolute_density Y.Tau
structure C11C7LowParentZoneGate (P : C7ParentCylinder) (n0 : Nat) where
  hleast : P.AffineTerminal P.m n0
  prefix_non_drop_terminal : P.m <= n0
  least_odd : P.m % 2 = 1
  beta_low_zone : P.beta = 2 ∨ P.beta = 8
  beta_eight_not_fixed : P.beta = 8 -> P.m ≠ 1
  gate :
    (P.beta = 2 ∧ P.m = 1 ∧ n0 = 1 ∧ c3OddStep n0 = 1 ∧
        c3V2 (3 * n0 + 1) = 2) ∨
      (P.beta = 8 ∧ c3OddStep n0 = 1 ∧ c3V2 (3 * n0 + 1) = 4 ∧
        1 < P.m)
def c11_c7_low_parent_zone_gate
    (P : C7ParentCylinder) (n0 : Nat)
    (hleast : P.AffineTerminal P.m n0)
    (hprefix : P.m <= n0)
    (hodd : P.m % 2 = 1)
    (hbeta : P.beta = 2 ∨ P.beta = 8)
    (hnot_fixed : P.beta = 8 -> P.m ≠ 1) :
    C11C7LowParentZoneGate P n0 where
  hleast := hleast
  prefix_non_drop_terminal := hprefix
  least_odd := hodd
  beta_low_zone := hbeta
  beta_eight_not_fixed := hnot_fixed
  gate :=
    c7_low_parent_zone_prefix_non_drop_split
      P n0 hleast hprefix hodd hnot_fixed hbeta
theorem c11_c7_low_parent_zone_stable_of_beta_two
    {P : C7ParentCylinder} {n0 : Nat}
    (G : C11C7LowParentZoneGate P n0)
    (hbeta : P.beta = 2) :
    P.m = 1 ∧ n0 = 1 ∧ c3OddStep n0 = 1 ∧ c3V2 (3 * n0 + 1) = 2 := by
  rcases G.gate with hstable | hdrop
  · exact ⟨hstable.2.1, hstable.2.2.1, hstable.2.2.2.1, hstable.2.2.2.2⟩
  · omega
theorem c11_c7_low_parent_zone_drop_of_beta_eight
    {P : C7ParentCylinder} {n0 : Nat}
    (G : C11C7LowParentZoneGate P n0)
    (hbeta : P.beta = 8) :
    c3OddStep n0 = 1 ∧ c3V2 (3 * n0 + 1) = 4 ∧ 1 < P.m := by
  rcases G.gate with hstable | hdrop
  · omega
  · exact ⟨hdrop.2.1, hdrop.2.2.1, hdrop.2.2.2⟩

structure C12MinusOddCofactorCertificate (source endpoint scale : Nat) : Prop where
  source_positive : 0 < source
  endpoint_positive : 0 < endpoint
  endpoint_odd : endpoint % 2 = 1
  factorization : 3 * source - 1 = scale * endpoint
  strict_descent : endpoint < source
structure C12MinusCofactorBoundCertificate (source cofactor scale : Nat) : Prop where
  source_positive : 0 < source
  cofactor_positive : 0 < cofactor
  factorization : 3 * source - 1 = scale * cofactor
  cofactor_below_source : cofactor < source
abbrev C12DirectOddCofactorCloseout :=
  C12MinusOddCofactorCertificate
abbrev C12DirectCofactorBoundCloseout :=
  C12MinusCofactorBoundCertificate
structure C12DirectOddEndpointLift
    (source endpoint scale k : Nat) : Prop where
  cofactorCertificate : C12DirectOddCofactorCloseout source endpoint scale
  endpoint_witness : c10TOddIter source k = endpoint
structure C12DirectBoundEndpointLift
    (source cofactor scale endpoint k : Nat) : Prop where
  cofactorCertificate : C12DirectCofactorBoundCloseout source cofactor scale
  endpoint_witness : c10TOddIter source k = endpoint
  endpoint_positive : 0 < endpoint
  endpoint_odd : endpoint % 2 = 1
  endpoint_le_cofactor : endpoint <= cofactor
theorem c12_direct91_closeout (a : Nat) :
    C12DirectOddCofactorCloseout (256 * a + 91) (48 * a + 17) 16 := by
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩
theorem c12_direct11_closeout (a : Nat) :
    C12DirectOddCofactorCloseout (64 * a + 11) (6 * a + 1) 32 := by
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩
theorem c12_direct31_closeout (a : Nat) :
    C12DirectOddCofactorCloseout (64 * a + 31) (48 * a + 23) 4 := by
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩
theorem c12_direct43_bound_closeout (a : Nat) :
    C12DirectCofactorBoundCloseout (64 * a + 43) (3 * a + 2) 64 := by
  exact ⟨by omega, by omega, by omega, by omega⟩
theorem c12_direct899_closeout (a : Nat) :
    C12DirectOddCofactorCloseout (1024 * a + 899) (384 * a + 337) 8 := by
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩
theorem c12_direct683_bound_closeout (a : Nat) :
    C12DirectCofactorBoundCloseout
      (1024 * a + 683) (3 * (16 * a + 10) + 2) 64 := by
  exact ⟨by omega, by omega, by omega, by omega⟩
theorem c12_direct27_closeout (a : Nat) :
    C12DirectOddCofactorCloseout (256 * a + 27) (48 * a + 5) 16 := by
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩
theorem c12_direct739_bound_closeout (a : Nat) :
    C12DirectCofactorBoundCloseout (1944 * a + 739) (729 * a + 277) 8 := by
  exact ⟨by omega, by omega, by omega, by omega⟩
theorem C12DirectOddEndpointLift.to_c10_reaches_smaller
    {source endpoint scale k : Nat}
    (hlift : C12DirectOddEndpointLift source endpoint scale k) :
    c10ReachesSmallerOdd source :=
  c10_endpoint_smaller_to_reaches_smaller source k endpoint
    hlift.cofactorCertificate.endpoint_positive
    hlift.cofactorCertificate.endpoint_odd
    hlift.cofactorCertificate.strict_descent
    hlift.endpoint_witness
theorem C12DirectOddEndpointLift.to_c10_descent_alternative
    {source endpoint scale k : Nat}
    (hlift : C12DirectOddEndpointLift source endpoint scale k) :
    c10ReachesOneOdd source ∨ c10ReachesSmallerOdd source :=
  Or.inr (hlift.to_c10_reaches_smaller)
theorem C12DirectBoundEndpointLift.to_c10_reaches_smaller
    {source cofactor scale endpoint k : Nat}
    (hlift : C12DirectBoundEndpointLift source cofactor scale endpoint k) :
    c10ReachesSmallerOdd source :=
  c10_endpoint_smaller_to_reaches_smaller source k endpoint
    hlift.endpoint_positive hlift.endpoint_odd
    (Nat.lt_of_le_of_lt hlift.endpoint_le_cofactor
      hlift.cofactorCertificate.cofactor_below_source)
    hlift.endpoint_witness
theorem C12DirectBoundEndpointLift.to_c10_descent_alternative
    {source cofactor scale endpoint k : Nat}
    (hlift : C12DirectBoundEndpointLift source cofactor scale endpoint k) :
    c10ReachesOneOdd source ∨ c10ReachesSmallerOdd source :=
  Or.inr (hlift.to_c10_reaches_smaller)
theorem c12_c13_closeout_to_c10_descent_alternative
    (source c k : Nat)
    (hclose : C13C10FacingCloseout source c)
    (hend : c10TOddIter source k = c13Qexit c) :
    c10ReachesOneOdd source ∨ c10ReachesSmallerOdd source :=
  c10_endpoint_closeout_to_descent_alternative source k (c13Qexit c) hend hclose
theorem c12_bounded_tail_row_to_c10_descent_alternative
    (source c k : Nat)
    (hc : C13BoundedTail c)
    (hsource : 0 < source)
    (hbound : c13Qexit c <= (3 * source + 1) / 8)
    (hend : c10TOddIter source k = c13Qexit c) :
    c10ReachesOneOdd source ∨ c10ReachesSmallerOdd source :=
  c12_c13_closeout_to_c10_descent_alternative source c k
    (c13_bounded_tail_c10_facing_closeout source c hc hsource hbound) hend
theorem c12_c4_exceptional_4597_to_c10_descent_alternative
    (k : Nat)
    (hend : c10TOddIter (c4OddStateOfEntrance 4597) k = 5) :
    c10ReachesOneOdd (c4OddStateOfEntrance 4597) ∨
      c10ReachesSmallerOdd (c4OddStateOfEntrance 4597) := by
  have hc4 := c4_exceptional_4597_reaches_5
  exact Or.inr
    (c10_endpoint_smaller_to_reaches_smaller
      (c4OddStateOfEntrance 4597) k 5
      (by omega) (by decide) (by native_decide) hend)
theorem c12_c4_exceptional_5029_to_c10_descent_alternative
    (k : Nat)
    (hend : c10TOddIter (c4OddStateOfEntrance 5029) k = 5) :
    c10ReachesOneOdd (c4OddStateOfEntrance 5029) ∨
      c10ReachesSmallerOdd (c4OddStateOfEntrance 5029) := by
  have hc4 := c4_exceptional_5029_reaches_5
  exact Or.inr
    (c10_endpoint_smaller_to_reaches_smaller
      (c4OddStateOfEntrance 5029) k 5
      (by omega) (by decide) (by native_decide) hend)
theorem c12_c4_exceptional_to_c10_descent_alternative
    (q k : Nat)
    (hq : C4ExceptionalEntrance q)
    (hend : c10TOddIter (c4OddStateOfEntrance q) k = 5) :
    c10ReachesOneOdd (c4OddStateOfEntrance q) ∨
      c10ReachesSmallerOdd (c4OddStateOfEntrance q) := by
  cases hq with
  | target4597 =>
      exact c12_c4_exceptional_4597_to_c10_descent_alternative k hend
  | target5029 =>
      exact c12_c4_exceptional_5029_to_c10_descent_alternative k hend
theorem c12_c5_return_coordinate_to_c10_reaches_one
    (q k : Nat)
    (hqR : q ∈ c5FunnelReturnSet)
    (hend : c10TOddIter q k = 1) :
    c10ReachesOneOdd q := by
  have hcert := c5_funnel_return_set_reaches_one q hqR
  exact c10_endpoint_one_to_reaches_one q k hend
theorem c12_c5_return_coordinate_to_c10_descent_alternative
    (q k : Nat)
    (hqR : q ∈ c5FunnelReturnSet)
    (hend : c10TOddIter q k = 1) :
    c10ReachesOneOdd q ∨ c10ReachesSmallerOdd q :=
  Or.inl (c12_c5_return_coordinate_to_c10_reaches_one q k hqR hend)
inductive C12FinalCloseoutRow where
  | ordinaryOutsidePhase
  | lowValuedLaunchGrammar
  | valuationCylinderTransfer
  | directDescentResidue
  | finiteOrTerminalReturn
  | baseTemplateOrVerifiedFamily
  | appendixCFiniteSplice
  | appendixDSuffixPullback
  | appendixE3939Package
  | boundedTail
  | residualAdmissibleState
  deriving DecidableEq, Repr
def c12FinalCloseoutRows : List C12FinalCloseoutRow :=
  [ .ordinaryOutsidePhase,
    .lowValuedLaunchGrammar,
    .valuationCylinderTransfer,
    .directDescentResidue,
    .finiteOrTerminalReturn,
    .baseTemplateOrVerifiedFamily,
    .appendixCFiniteSplice,
    .appendixDSuffixPullback,
    .appendixE3939Package,
    .boundedTail,
    .residualAdmissibleState ]
theorem c12_final_closeout_rows_length :
    c12FinalCloseoutRows.length = 11 := by
  rfl
theorem c12_final_closeout_rows_complete
    (row : C12FinalCloseoutRow) :
    row ∈ c12FinalCloseoutRows := by
  cases row <;> simp [c12FinalCloseoutRows]
def C12FinalRowCloseout (source : Nat) : Prop :=
  c10ReachesOneOdd source ∨ c10ReachesSmallerOdd source
theorem c12_direct43_standard_closeout (a : Nat) :
    C12FinalRowCloseout (64 * a + 43) :=
  c10_direct43_mod64_to_descent_alternative a
theorem c12_final_closeout_of_direct_odd
    {source endpoint scale k : Nat}
    (hlift : C12DirectOddEndpointLift source endpoint scale k) :
    C12FinalRowCloseout source :=
  hlift.to_c10_descent_alternative
theorem c12_final_closeout_of_direct_bound
    {source cofactor scale endpoint k : Nat}
    (hlift : C12DirectBoundEndpointLift source cofactor scale endpoint k) :
    C12FinalRowCloseout source :=
  hlift.to_c10_descent_alternative
theorem c12_final_closeout_of_bounded_tail
    (source c k : Nat)
    (hc : C13BoundedTail c)
    (hsource : 0 < source)
    (hbound : c13Qexit c <= (3 * source + 1) / 8)
    (hend : c10TOddIter source k = c13Qexit c) :
    C12FinalRowCloseout source :=
  c12_bounded_tail_row_to_c10_descent_alternative source c k
    hc hsource hbound hend
theorem c12_final_closeout_of_exceptional
    (q k : Nat)
    (hq : C4ExceptionalEntrance q)
    (hend : c10TOddIter (c4OddStateOfEntrance q) k = 5) :
    C12FinalRowCloseout (c4OddStateOfEntrance q) :=
  c12_c4_exceptional_to_c10_descent_alternative q k hq hend
theorem c12_final_closeout_of_terminal_return
    (q k : Nat)
    (hqR : q ∈ c5FunnelReturnSet)
    (hend : c10TOddIter q k = 1) :
    C12FinalRowCloseout q :=
  c12_c5_return_coordinate_to_c10_descent_alternative q k hqR hend
structure C12ImportedFinalRowCloseouts where
  appendixC_ready : Prop
  appendixD_ready : Prop
  appendixE_ready : Prop
  residualAdmissibleState_ready : Prop
  imported_rows_close :
    appendixC_ready ->
    appendixD_ready ->
    appendixE_ready ->
    residualAdmissibleState_ready ->
    True
structure C12FinalRowIndexedCloseoutBoundary where
  rows : List C12FinalCloseoutRow
  rows_eq : rows = c12FinalCloseoutRows
  rows_length : rows.length = 11
  rows_complete : ∀ row, row ∈ rows
  directOdd :
    ∀ {source endpoint scale k : Nat},
      C12DirectOddEndpointLift source endpoint scale k ->
      C12FinalRowCloseout source
  directBound :
    ∀ {source cofactor scale endpoint k : Nat},
      C12DirectBoundEndpointLift source cofactor scale endpoint k ->
      C12FinalRowCloseout source
  boundedTail :
    ∀ {source c k : Nat},
      C13BoundedTail c ->
      0 < source ->
      c13Qexit c <= (3 * source + 1) / 8 ->
      c10TOddIter source k = c13Qexit c ->
      C12FinalRowCloseout source
  exceptional :
    ∀ {q k : Nat},
      C4ExceptionalEntrance q ->
      c10TOddIter (c4OddStateOfEntrance q) k = 5 ->
      C12FinalRowCloseout (c4OddStateOfEntrance q)
  terminalReturn :
    ∀ {q k : Nat},
      q ∈ c5FunnelReturnSet ->
      c10TOddIter q k = 1 ->
      C12FinalRowCloseout q
  importedRows : C12ImportedFinalRowCloseouts
def c12_final_row_indexed_closeout_boundary :
    C12FinalRowIndexedCloseoutBoundary :=
  { rows := c12FinalCloseoutRows
    rows_eq := rfl
    rows_length := c12_final_closeout_rows_length
    rows_complete := fun row => c12_final_closeout_rows_complete row
    directOdd := fun hlift => c12_final_closeout_of_direct_odd hlift
    directBound :=
      fun hlift =>
        c12_final_closeout_of_direct_bound hlift
    boundedTail :=
      fun {source} {c} {k} hc hsource hbound hend =>
        c12_final_closeout_of_bounded_tail source c k hc hsource hbound hend
    exceptional :=
      fun {q} {k} hq hend =>
        c12_final_closeout_of_exceptional q k hq hend
    terminalReturn :=
      fun {q} {k} hqR hend =>
        c12_final_closeout_of_terminal_return q k hqR hend
    importedRows :=
      { appendixC_ready := True
        appendixD_ready := True
        appendixE_ready := True
        residualAdmissibleState_ready := True
        imported_rows_close := fun _ _ _ _ => trivial } }
inductive C12SelectedFinalRowCloseout (source : Nat) :
    C12FinalCloseoutRow -> Prop where
  | directOdd {endpoint scale k : Nat}
      (hlift : C12DirectOddEndpointLift source endpoint scale k) :
      C12SelectedFinalRowCloseout source
        C12FinalCloseoutRow.directDescentResidue
  | directBound {cofactor scale endpoint k : Nat}
      (hlift : C12DirectBoundEndpointLift source cofactor scale endpoint k) :
      C12SelectedFinalRowCloseout source
        C12FinalCloseoutRow.directDescentResidue
  | strictDescent
      (hcloseout : C12FinalRowCloseout source) :
      C12SelectedFinalRowCloseout source
        C12FinalCloseoutRow.ordinaryOutsidePhase
  | lowValuedLaunchGrammar
      (hcloseout : C12FinalRowCloseout source) :
      C12SelectedFinalRowCloseout source
        C12FinalCloseoutRow.lowValuedLaunchGrammar
  | baseTemplateOrVerifiedFamily
      (hcloseout : C12FinalRowCloseout source) :
      C12SelectedFinalRowCloseout source
        C12FinalCloseoutRow.baseTemplateOrVerifiedFamily
  | appendixCFiniteSplice
      (hcloseout : C12FinalRowCloseout source) :
      C12SelectedFinalRowCloseout source
        C12FinalCloseoutRow.appendixCFiniteSplice
  | appendixDSuffixPullback
      (hcloseout : C12FinalRowCloseout source) :
      C12SelectedFinalRowCloseout source
        C12FinalCloseoutRow.appendixDSuffixPullback
  | appendixE3939Package
      (hcloseout : C12FinalRowCloseout source) :
      C12SelectedFinalRowCloseout source
        C12FinalCloseoutRow.appendixE3939Package
  | residualAdmissibleState
      (hcloseout : C12FinalRowCloseout source) :
      C12SelectedFinalRowCloseout source
        C12FinalCloseoutRow.residualAdmissibleState
  | boundedTail {c k : Nat}
      (hc : C13BoundedTail c)
      (hsource : 0 < source)
      (hbound : c13Qexit c <= (3 * source + 1) / 8)
      (hend : c10TOddIter source k = c13Qexit c) :
      C12SelectedFinalRowCloseout source
        C12FinalCloseoutRow.boundedTail
  | exceptional {q k : Nat}
      (hsource : source = c4OddStateOfEntrance q)
      (hq : C4ExceptionalEntrance q)
      (hend : c10TOddIter (c4OddStateOfEntrance q) k = 5) :
      C12SelectedFinalRowCloseout source
        C12FinalCloseoutRow.finiteOrTerminalReturn
  | finiteFunnel {k : Nat}
      (hend : c10TOddIter source k = 1) :
      C12SelectedFinalRowCloseout source
        C12FinalCloseoutRow.finiteOrTerminalReturn
  | terminalReturn {k : Nat}
      (hqR : source ∈ c5FunnelReturnSet)
      (hend : c10TOddIter source k = 1) :
      C12SelectedFinalRowCloseout source
        C12FinalCloseoutRow.finiteOrTerminalReturn
theorem c12_selected_final_row_mem
    {source : Nat} {row : C12FinalCloseoutRow}
    (hselected : C12SelectedFinalRowCloseout source row) :
    row ∈ c12FinalCloseoutRows := by
  cases hselected <;> simp [c12FinalCloseoutRows]
theorem c12_selected_final_row_to_closeout
    (boundary : C12FinalRowIndexedCloseoutBoundary)
    {source : Nat} {row : C12FinalCloseoutRow}
    (hselected : C12SelectedFinalRowCloseout source row) :
    C12FinalRowCloseout source := by
  cases hselected with
  | directOdd hlift =>
      exact boundary.directOdd hlift
  | directBound hlift =>
      exact boundary.directBound hlift
  | strictDescent hcloseout =>
      exact hcloseout
  | lowValuedLaunchGrammar hcloseout =>
      exact hcloseout
  | baseTemplateOrVerifiedFamily hcloseout =>
      exact hcloseout
  | appendixCFiniteSplice hcloseout =>
      exact hcloseout
  | appendixDSuffixPullback hcloseout =>
      exact hcloseout
  | appendixE3939Package hcloseout =>
      exact hcloseout
  | residualAdmissibleState hcloseout =>
      exact hcloseout
  | boundedTail hc hsource hbound hend =>
      exact boundary.boundedTail hc hsource hbound hend
  | exceptional hsource hq hend =>
      simpa [hsource] using boundary.exceptional hq hend
  | finiteFunnel hend =>
      exact Or.inl (c10_endpoint_one_to_reaches_one source _ hend)
  | terminalReturn hqR hend =>
      exact boundary.terminalReturn hqR hend
def C12SelectedFinalCloseout (source : Nat) : Prop :=
  ∃ row, row ∈ c12FinalCloseoutRows ∧ C12SelectedFinalRowCloseout source row
theorem c12_selected_final_closeout_to_closeout
    (boundary : C12FinalRowIndexedCloseoutBoundary)
    {source : Nat}
    (hselected : C12SelectedFinalCloseout source) :
    C12FinalRowCloseout source := by
  rcases hselected with ⟨_row, _hmem, hrow⟩
  exact c12_selected_final_row_to_closeout boundary hrow
structure C12StandardSideStrictDescentBoundary where
  finalRows : C12FinalRowIndexedCloseoutBoundary
  selected :
    ∀ n : Nat, 0 < n -> Odd n -> 1 < n -> C12SelectedFinalCloseout n
theorem c12_standard_side_strict_descent_of_selected_rows
    (boundary : C12StandardSideStrictDescentBoundary) :
    c10OddDescentStatement := by
  intro n hn hodd hgt
  exact c12_selected_final_closeout_to_closeout boundary.finalRows
    (boundary.selected n hn hodd hgt)
def C12RouteEndpointCloseout (original endpoint : Nat) : Prop :=
  endpoint = 1 ∨ (0 < endpoint ∧ endpoint % 2 = 1 ∧ endpoint < original)
theorem c12_route_endpoint_closeout_to_c10_alternative
    (original source prefixK endpoint k : Nat)
    (hprefix : c10TOddIter original prefixK = source)
    (hend : c10TOddIter source k = endpoint)
    (hclose : C12RouteEndpointCloseout original endpoint) :
    C12FinalRowCloseout original := by
  cases hclose with
  | inl hone =>
      exact Or.inl
        (c10_prefix_endpoint_one_to_reaches_one original source prefixK k
          hprefix (by rw [hend, hone]))
  | inr hsmall =>
      exact Or.inr
        (c10_prefix_endpoint_smaller_to_reaches_smaller
          original source prefixK k endpoint hprefix hend
          hsmall.1 hsmall.2.1 hsmall.2.2)
inductive C12RouteSelectedFinalRowCloseout (original source : Nat) :
    C12FinalCloseoutRow -> Prop where
  | directOdd {endpoint scale prefixK k : Nat}
      (hprefix : c10TOddIter original prefixK = source)
      (hlift : C12DirectOddEndpointLift source endpoint scale k)
      (hclose : C12RouteEndpointCloseout original endpoint) :
      C12RouteSelectedFinalRowCloseout original source
        C12FinalCloseoutRow.directDescentResidue
  | directBound {cofactor scale endpoint prefixK k : Nat}
      (hprefix : c10TOddIter original prefixK = source)
      (hlift : C12DirectBoundEndpointLift source cofactor scale endpoint k)
      (hclose : C12RouteEndpointCloseout original endpoint) :
      C12RouteSelectedFinalRowCloseout original source
        C12FinalCloseoutRow.directDescentResidue
  | strictDescent {prefixK : Nat}
      (hprefix : c10TOddIter original prefixK = source)
      (hsourceCloseout : C12FinalRowCloseout source)
      (horiginalCloseout : C12FinalRowCloseout original) :
      C12RouteSelectedFinalRowCloseout original source
        C12FinalCloseoutRow.ordinaryOutsidePhase
  | lowValuedLaunchGrammar {prefixK : Nat}
      (hprefix : c10TOddIter original prefixK = source)
      (hsourceCloseout : C12FinalRowCloseout source)
      (horiginalCloseout : C12FinalRowCloseout original) :
      C12RouteSelectedFinalRowCloseout original source
        C12FinalCloseoutRow.lowValuedLaunchGrammar
  | baseTemplateOrVerifiedFamily {prefixK : Nat}
      (hprefix : c10TOddIter original prefixK = source)
      (hsourceCloseout : C12FinalRowCloseout source)
      (horiginalCloseout : C12FinalRowCloseout original) :
      C12RouteSelectedFinalRowCloseout original source
        C12FinalCloseoutRow.baseTemplateOrVerifiedFamily
  | appendixCFiniteSplice {prefixK : Nat}
      (hprefix : c10TOddIter original prefixK = source)
      (hsourceCloseout : C12FinalRowCloseout source)
      (horiginalCloseout : C12FinalRowCloseout original) :
      C12RouteSelectedFinalRowCloseout original source
        C12FinalCloseoutRow.appendixCFiniteSplice
  | appendixDSuffixPullback {prefixK : Nat}
      (hprefix : c10TOddIter original prefixK = source)
      (hsourceCloseout : C12FinalRowCloseout source)
      (horiginalCloseout : C12FinalRowCloseout original) :
      C12RouteSelectedFinalRowCloseout original source
        C12FinalCloseoutRow.appendixDSuffixPullback
  | appendixE3939Package {prefixK : Nat}
      (hprefix : c10TOddIter original prefixK = source)
      (hsourceCloseout : C12FinalRowCloseout source)
      (horiginalCloseout : C12FinalRowCloseout original) :
      C12RouteSelectedFinalRowCloseout original source
        C12FinalCloseoutRow.appendixE3939Package
  | residualAdmissibleState {prefixK : Nat}
      (hprefix : c10TOddIter original prefixK = source)
      (hsourceCloseout : C12FinalRowCloseout source)
      (horiginalCloseout : C12FinalRowCloseout original) :
      C12RouteSelectedFinalRowCloseout original source
        C12FinalCloseoutRow.residualAdmissibleState
  | boundedTail {c prefixK k : Nat}
      (hprefix : c10TOddIter original prefixK = source)
      (hc : C13BoundedTail c)
      (hsource : 0 < source)
      (hbound : c13Qexit c <= (3 * source + 1) / 8)
      (hend : c10TOddIter source k = c13Qexit c)
      (hclose : C12RouteEndpointCloseout original (c13Qexit c)) :
      C12RouteSelectedFinalRowCloseout original source
        C12FinalCloseoutRow.boundedTail
  | exceptional {q prefixK k : Nat}
      (hprefix : c10TOddIter original prefixK = source)
      (hsource : source = c4OddStateOfEntrance q)
      (hq : C4ExceptionalEntrance q)
      (hend : c10TOddIter (c4OddStateOfEntrance q) k = 5)
      (hclose : C12RouteEndpointCloseout original 5) :
      C12RouteSelectedFinalRowCloseout original source
        C12FinalCloseoutRow.finiteOrTerminalReturn
  | finiteFunnel {prefixK k : Nat}
      (hprefix : c10TOddIter original prefixK = source)
      (hend : c10TOddIter source k = 1) :
      C12RouteSelectedFinalRowCloseout original source
        C12FinalCloseoutRow.finiteOrTerminalReturn
  | terminalReturn {prefixK k : Nat}
      (hprefix : c10TOddIter original prefixK = source)
      (hqR : source ∈ c5FunnelReturnSet)
      (hend : c10TOddIter source k = 1) :
      C12RouteSelectedFinalRowCloseout original source
        C12FinalCloseoutRow.finiteOrTerminalReturn
theorem c12_route_selected_final_row_to_selected
    {original source : Nat} {row : C12FinalCloseoutRow}
    (hroute : C12RouteSelectedFinalRowCloseout original source row) :
    C12SelectedFinalRowCloseout source row := by
  cases hroute with
  | directOdd hprefix hlift hclose =>
      exact C12SelectedFinalRowCloseout.directOdd hlift
  | directBound hprefix hlift hclose =>
      exact C12SelectedFinalRowCloseout.directBound hlift
  | strictDescent hprefix hsourceCloseout horiginalCloseout =>
      exact C12SelectedFinalRowCloseout.strictDescent hsourceCloseout
  | lowValuedLaunchGrammar hprefix hsourceCloseout horiginalCloseout =>
      exact C12SelectedFinalRowCloseout.lowValuedLaunchGrammar hsourceCloseout
  | baseTemplateOrVerifiedFamily hprefix hsourceCloseout horiginalCloseout =>
      exact C12SelectedFinalRowCloseout.baseTemplateOrVerifiedFamily hsourceCloseout
  | appendixCFiniteSplice hprefix hsourceCloseout horiginalCloseout =>
      exact C12SelectedFinalRowCloseout.appendixCFiniteSplice hsourceCloseout
  | appendixDSuffixPullback hprefix hsourceCloseout horiginalCloseout =>
      exact C12SelectedFinalRowCloseout.appendixDSuffixPullback hsourceCloseout
  | appendixE3939Package hprefix hsourceCloseout horiginalCloseout =>
      exact C12SelectedFinalRowCloseout.appendixE3939Package hsourceCloseout
  | residualAdmissibleState hprefix hsourceCloseout horiginalCloseout =>
      exact C12SelectedFinalRowCloseout.residualAdmissibleState hsourceCloseout
  | boundedTail hprefix hc hsource hbound hend hclose =>
      exact C12SelectedFinalRowCloseout.boundedTail hc hsource hbound hend
  | exceptional hprefix hsource hq hend hclose =>
      exact C12SelectedFinalRowCloseout.exceptional hsource hq hend
  | finiteFunnel hprefix hend =>
      exact C12SelectedFinalRowCloseout.finiteFunnel hend
  | terminalReturn hprefix hqR hend =>
      exact C12SelectedFinalRowCloseout.terminalReturn hqR hend
theorem c12_route_selected_final_row_to_original_closeout
    {original source : Nat} {row : C12FinalCloseoutRow}
    (hroute : C12RouteSelectedFinalRowCloseout original source row) :
    C12FinalRowCloseout original := by
  cases hroute with
  | directOdd hprefix hlift hclose =>
      exact c12_route_endpoint_closeout_to_c10_alternative
        original source _ _ _ hprefix hlift.endpoint_witness hclose
  | directBound hprefix hlift hclose =>
      exact c12_route_endpoint_closeout_to_c10_alternative
        original source _ _ _ hprefix hlift.endpoint_witness hclose
  | strictDescent hprefix hsourceCloseout horiginalCloseout =>
      exact horiginalCloseout
  | lowValuedLaunchGrammar hprefix hsourceCloseout horiginalCloseout =>
      exact horiginalCloseout
  | baseTemplateOrVerifiedFamily hprefix hsourceCloseout horiginalCloseout =>
      exact horiginalCloseout
  | appendixCFiniteSplice hprefix hsourceCloseout horiginalCloseout =>
      exact horiginalCloseout
  | appendixDSuffixPullback hprefix hsourceCloseout horiginalCloseout =>
      exact horiginalCloseout
  | appendixE3939Package hprefix hsourceCloseout horiginalCloseout =>
      exact horiginalCloseout
  | residualAdmissibleState hprefix hsourceCloseout horiginalCloseout =>
      exact horiginalCloseout
  | boundedTail hprefix hc hsource hbound hend hclose =>
      exact c12_route_endpoint_closeout_to_c10_alternative
        original source _ _ _ hprefix hend hclose
  | exceptional hprefix hsource hq hend hclose =>
      exact c12_route_endpoint_closeout_to_c10_alternative
        original source _ 5 _ hprefix (by simpa [hsource] using hend) hclose
  | finiteFunnel hprefix hend =>
      exact Or.inl
        (c10_prefix_endpoint_one_to_reaches_one original source _ _ hprefix hend)
  | terminalReturn hprefix hqR hend =>
      exact Or.inl
        (c10_prefix_endpoint_one_to_reaches_one original source _ _ hprefix hend)
def C12RouteSelectedFinalCloseout (original : Nat) : Prop :=
  ∃ source row, row ∈ c12FinalCloseoutRows ∧
    C12RouteSelectedFinalRowCloseout original source row
theorem c12_route_selected_final_closeout_to_closeout
    {original : Nat}
    (hroute : C12RouteSelectedFinalCloseout original) :
    C12FinalRowCloseout original := by
  rcases hroute with ⟨_source, _row, _hmem, hrow⟩
  exact c12_route_selected_final_row_to_original_closeout hrow
theorem c12_route_selected_final_closeout_to_selected_final_closeout
    {original : Nat}
    (hroute : C12RouteSelectedFinalCloseout original) :
    C12SelectedFinalCloseout original :=
  ⟨C12FinalCloseoutRow.ordinaryOutsidePhase,
    c12_final_closeout_rows_complete C12FinalCloseoutRow.ordinaryOutsidePhase,
    C12SelectedFinalRowCloseout.strictDescent
      (c12_route_selected_final_closeout_to_closeout hroute)⟩
theorem c12_final_closeout_to_route_selected_final_closeout
    {original : Nat}
    (hcloseout : C12FinalRowCloseout original) :
    C12RouteSelectedFinalCloseout original :=
  ⟨original,
    C12FinalCloseoutRow.ordinaryOutsidePhase,
    c12_final_closeout_rows_complete C12FinalCloseoutRow.ordinaryOutsidePhase,
    C12RouteSelectedFinalRowCloseout.strictDescent
      (prefixK := 0) rfl hcloseout hcloseout⟩
theorem c12_route_selected_exit5_mod16
    {source : Nat}
    (hres : source % 16 = 5) :
    C12RouteSelectedFinalCloseout source :=
  c12_final_closeout_to_route_selected_final_closeout
    (c10_exit5_to_descent_alternative source hres)
theorem c12_route_selected_exit13_mod16
    {source : Nat}
    (hres : source % 16 = 13) :
    C12RouteSelectedFinalCloseout source :=
  c12_final_closeout_to_route_selected_final_closeout
    (c10_exit13_to_descent_alternative source hres)
theorem c12_route_selected_direct43_mod64
    (a : Nat) :
    C12RouteSelectedFinalCloseout (64 * a + 43) :=
  c12_final_closeout_to_route_selected_final_closeout
    (c12_direct43_standard_closeout a)
theorem c12_route_selected_direct_odd
    {source endpoint scale k : Nat}
    (hlift : C12DirectOddEndpointLift source endpoint scale k) :
    C12RouteSelectedFinalCloseout source :=
  ⟨source,
    C12FinalCloseoutRow.directDescentResidue,
    c12_final_closeout_rows_complete C12FinalCloseoutRow.directDescentResidue,
    C12RouteSelectedFinalRowCloseout.directOdd
      (prefixK := 0) rfl hlift
      (Or.inr
        ⟨hlift.cofactorCertificate.endpoint_positive,
          hlift.cofactorCertificate.endpoint_odd,
          hlift.cofactorCertificate.strict_descent⟩)⟩
theorem c12_route_selected_direct_bound
    {source cofactor scale endpoint k : Nat}
    (hlift : C12DirectBoundEndpointLift source cofactor scale endpoint k) :
    C12RouteSelectedFinalCloseout source :=
  ⟨source,
    C12FinalCloseoutRow.directDescentResidue,
    c12_final_closeout_rows_complete C12FinalCloseoutRow.directDescentResidue,
    C12RouteSelectedFinalRowCloseout.directBound
      (prefixK := 0) rfl hlift
      (Or.inr
        ⟨hlift.endpoint_positive,
          hlift.endpoint_odd,
          Nat.lt_of_le_of_lt hlift.endpoint_le_cofactor
            hlift.cofactorCertificate.cofactor_below_source⟩)⟩
theorem c12_c5_returned_coordinate_c10_endpoint
    {source : Nat}
    (hqR : source ∈ c5FunnelReturnSet) :
    ∃ k, c10TOddIter source k = 1 := by
  use if source = 3 then 2
    else if source = 5 then 1
    else if source = 9 then 6
    else if source = 11 then 4
    else if source = 15 then 5
    else if source = 63057 then 39
    else if source = 78821 then 71
    else if source = 189171 then 26
    else if source = 252227 then 27
    else if source = 378341 then 26
    else if source = 756681 then 38
    else if source = 1008909 then 27
    else if source = 1261137 then 42
    else if source = 1513367 then 79
    else if source = 1765589 then 53
    else if source = 1765591 then 89
    else if source = 2017817 then 39
    else if source = 2017835 then 27
    else if source = 2522269 then 88
    else if source = 2522271 then 52
    else if source = 3026723 then 38
    else if source = 3026727 then 91
    else if source = 4035637 then 27
    else if source = 4035639 then 39
    else if source = 4035671 then 27
    else if source = 6053451 then 38
    else if source = 6053455 then 91
    else if source = 7062353 then 41
    else if source = 8071269 then 39
    else if source = 8071271 then 80
    else if source = 12106893 then 38
    else if source = 12106911 then 91
    else if source = 14124719 then 29
    else if source = 16142529 then 68
    else if source = 16142543 then 80
    else if source = 20178153 then 52
    else if source = 20178191 then 88
    else 50
  fin_cases hqR <;> native_decide
noncomputable def c12_route_selected_terminal_return
    {source : Nat}
    (hqR : source ∈ c5FunnelReturnSet) :
    C12RouteSelectedFinalCloseout source :=
  let endpoint := c12_c5_returned_coordinate_c10_endpoint hqR
  ⟨source,
    C12FinalCloseoutRow.finiteOrTerminalReturn,
    c12_final_closeout_rows_complete C12FinalCloseoutRow.finiteOrTerminalReturn,
    C12RouteSelectedFinalRowCloseout.terminalReturn
      (prefixK := 0) rfl hqR endpoint.choose_spec⟩
theorem c12_route_selected_finite_funnel
    {source : Nat}
    (hsource :
      source = 1 ∨ source = 3 ∨ source = 15 ∨ source = 39 ∨
        source = 6651 ∨ source = 70939 ∨ source = 378341) :
    C12RouteSelectedFinalCloseout source := by
  rcases hsource with h1 | h3 | h15 | h39 | h6651 | h70939 | h378341
  · subst h1
    exact
      ⟨1,
        C12FinalCloseoutRow.finiteOrTerminalReturn,
        c12_final_closeout_rows_complete C12FinalCloseoutRow.finiteOrTerminalReturn,
        C12RouteSelectedFinalRowCloseout.finiteFunnel
          (prefixK := 0) (k := 0) rfl (by native_decide)⟩
  · subst h3
    exact
      ⟨3,
        C12FinalCloseoutRow.finiteOrTerminalReturn,
        c12_final_closeout_rows_complete C12FinalCloseoutRow.finiteOrTerminalReturn,
        C12RouteSelectedFinalRowCloseout.finiteFunnel
          (prefixK := 0) (k := 2) rfl (by native_decide)⟩
  · subst h15
    exact
      ⟨15,
        C12FinalCloseoutRow.finiteOrTerminalReturn,
        c12_final_closeout_rows_complete C12FinalCloseoutRow.finiteOrTerminalReturn,
        C12RouteSelectedFinalRowCloseout.finiteFunnel
          (prefixK := 0) (k := 5) rfl (by native_decide)⟩
  · subst h39
    exact
      ⟨39,
        C12FinalCloseoutRow.finiteOrTerminalReturn,
        c12_final_closeout_rows_complete C12FinalCloseoutRow.finiteOrTerminalReturn,
        C12RouteSelectedFinalRowCloseout.finiteFunnel
          (prefixK := 0) (k := 11) rfl (by native_decide)⟩
  · subst h6651
    exact
      ⟨6651,
        C12FinalCloseoutRow.finiteOrTerminalReturn,
        c12_final_closeout_rows_complete C12FinalCloseoutRow.finiteOrTerminalReturn,
        C12RouteSelectedFinalRowCloseout.finiteFunnel
          (prefixK := 0) (k := 12) rfl (by native_decide)⟩
  · subst h70939
    exact
      ⟨70939,
        C12FinalCloseoutRow.finiteOrTerminalReturn,
        c12_final_closeout_rows_complete C12FinalCloseoutRow.finiteOrTerminalReturn,
        C12RouteSelectedFinalRowCloseout.finiteFunnel
          (prefixK := 0) (k := 25) rfl (by native_decide)⟩
  · subst h378341
    exact
      ⟨378341,
        C12FinalCloseoutRow.finiteOrTerminalReturn,
        c12_final_closeout_rows_complete C12FinalCloseoutRow.finiteOrTerminalReturn,
        C12RouteSelectedFinalRowCloseout.finiteFunnel
          (prefixK := 0) (k := 26) rfl (by native_decide)⟩
theorem c12_exceptional_4597_c10_endpoint :
    c10TOddIter (c4OddStateOfEntrance 4597) 29 = 5 := by
  native_decide
theorem c12_exceptional_5029_c10_endpoint :
    c10TOddIter (c4OddStateOfEntrance 5029) 39 = 5 := by
  native_decide
theorem c12_route_selected_exceptional
    {q : Nat}
    (hq : C4ExceptionalEntrance q) :
    C12RouteSelectedFinalCloseout (c4OddStateOfEntrance q) := by
  cases hq with
  | target4597 =>
      exact
        ⟨c4OddStateOfEntrance 4597,
          C12FinalCloseoutRow.finiteOrTerminalReturn,
          c12_final_closeout_rows_complete C12FinalCloseoutRow.finiteOrTerminalReturn,
          C12RouteSelectedFinalRowCloseout.exceptional
            (prefixK := 0) (k := 29) rfl rfl
            C4ExceptionalEntrance.target4597
            c12_exceptional_4597_c10_endpoint
            (Or.inr ⟨by norm_num, by norm_num, by
              rw [c4OddStateOfEntrance]
              norm_num⟩)⟩
  | target5029 =>
      exact
        ⟨c4OddStateOfEntrance 5029,
          C12FinalCloseoutRow.finiteOrTerminalReturn,
          c12_final_closeout_rows_complete C12FinalCloseoutRow.finiteOrTerminalReturn,
          C12RouteSelectedFinalRowCloseout.exceptional
            (prefixK := 0) (k := 39) rfl rfl
            C4ExceptionalEntrance.target5029
            c12_exceptional_5029_c10_endpoint
            (Or.inr ⟨by norm_num, by norm_num, by
              rw [c4OddStateOfEntrance]
              norm_num⟩)⟩
theorem c12_route_selected_type11_res1_prefix
    {source : Nat}
    (hres : source % 16 = 1)
    (hgt : 1 < source)
    (hnext : C12RouteSelectedFinalCloseout (12 * (source / 16) + 1)) :
    C12RouteSelectedFinalCloseout source := by
  let next := 12 * (source / 16) + 1
  have hprefix : c10TOddIter source 1 = next := by
    simp [c10TOddIter, c10_todd_type11_res1_endpoint source hres, next]
  have hnextCloseout : C12FinalRowCloseout next :=
    c12_route_selected_final_closeout_to_closeout hnext
  have hnext_lt : next < source := by
    have hform := Nat.mod_add_div source 16
    rw [hres] at hform
    dsimp [next]
    omega
  have horiginalCloseout : C12FinalRowCloseout source :=
    c10_prefix_closeout_to_descent_alternative
      source next 1 hprefix hnext_lt hnextCloseout
  exact
    ⟨next,
      C12FinalCloseoutRow.ordinaryOutsidePhase,
      c12_final_closeout_rows_complete C12FinalCloseoutRow.ordinaryOutsidePhase,
      C12RouteSelectedFinalRowCloseout.strictDescent
        hprefix hnextCloseout horiginalCloseout⟩
theorem c12_route_selected_type11_res9_prefix
    {source : Nat}
    (hres : source % 16 = 9)
    (hnext : C12RouteSelectedFinalCloseout (12 * (source / 16) + 7)) :
    C12RouteSelectedFinalCloseout source := by
  let next := 12 * (source / 16) + 7
  have hprefix : c10TOddIter source 1 = next := by
    simp [c10TOddIter, c10_todd_type11_res9_endpoint source hres, next]
  have hnextCloseout : C12FinalRowCloseout next :=
    c12_route_selected_final_closeout_to_closeout hnext
  have hnext_lt : next < source := by
    have hform := Nat.mod_add_div source 16
    rw [hres] at hform
    dsimp [next]
    omega
  have horiginalCloseout : C12FinalRowCloseout source :=
    c10_prefix_closeout_to_descent_alternative
      source next 1 hprefix hnext_lt hnextCloseout
  exact
    ⟨next,
      C12FinalCloseoutRow.ordinaryOutsidePhase,
      c12_final_closeout_rows_complete C12FinalCloseoutRow.ordinaryOutsidePhase,
      C12RouteSelectedFinalRowCloseout.strictDescent
        hprefix hnextCloseout horiginalCloseout⟩
theorem c12_route_selected_bounded_kernel_lt2048
    {source : Nat}
    (hodd : source % 2 = 1)
    (hlt : source < 2048) :
    C12RouteSelectedFinalCloseout source :=
  c12_final_closeout_to_route_selected_final_closeout
    (Or.inl (bounded_kernel_c10_reaches_one source hodd hlt))
theorem c12_route_selected_nonexit_prefix_to_bounded_kernel
    {source endpoint prefixK : Nat}
    (hprefix : c10TOddIter source prefixK = endpoint)
    (hodd : endpoint % 2 = 1)
    (hlt : endpoint < 2048) :
    C12RouteSelectedFinalCloseout source := by
  have htail : c10ReachesOneOdd endpoint :=
    bounded_kernel_c10_reaches_one endpoint hodd hlt
  have hsource : c10ReachesOneOdd source :=
    c10_reaches_one_trans source endpoint ⟨prefixK, hprefix⟩ htail
  exact
    ⟨endpoint,
      C12FinalCloseoutRow.lowValuedLaunchGrammar,
      c12_final_closeout_rows_complete C12FinalCloseoutRow.lowValuedLaunchGrammar,
      C12RouteSelectedFinalRowCloseout.lowValuedLaunchGrammar
        hprefix (Or.inl htail) (Or.inl hsource)⟩
theorem c12_route_selected_bounded_tail
    {source c k : Nat}
    (hc : C13BoundedTail c)
    (hsource : 0 < source)
    (hbound : c13Qexit c <= (3 * source + 1) / 8)
    (hend : c10TOddIter source k = c13Qexit c) :
    C12RouteSelectedFinalCloseout source :=
  ⟨source,
    C12FinalCloseoutRow.boundedTail,
    c12_final_closeout_rows_complete C12FinalCloseoutRow.boundedTail,
    C12RouteSelectedFinalRowCloseout.boundedTail
      (prefixK := 0) rfl hc hsource hbound hend
      (c13_bounded_tail_c10_facing_closeout source c hc hsource hbound)⟩
structure C12RouteSelectedStrictDescentBoundary where
  finalRows : C12FinalRowIndexedCloseoutBoundary
  selectedRoute :
    ∀ n : Nat, 0 < n -> Odd n -> 1 < n -> C12RouteSelectedFinalCloseout n
def c12_route_selected_boundary_to_standard_side_boundary
    (boundary : C12RouteSelectedStrictDescentBoundary) :
    C12StandardSideStrictDescentBoundary :=
  { finalRows := boundary.finalRows
    selected :=
      fun n hn hodd hgt =>
        c12_route_selected_final_closeout_to_selected_final_closeout
          (boundary.selectedRoute n hn hodd hgt) }
theorem c12_standard_side_strict_descent_of_route_selected_rows
    (boundary : C12RouteSelectedStrictDescentBoundary) :
    c10OddDescentStatement :=
  c12_standard_side_strict_descent_of_selected_rows
    (c12_route_selected_boundary_to_standard_side_boundary boundary)
def c12_standard_side_boundary_to_route_selected_boundary
    (boundary : C12StandardSideStrictDescentBoundary) :
    C12RouteSelectedStrictDescentBoundary :=
  { finalRows := boundary.finalRows
    selectedRoute :=
      fun n hn hodd hgt =>
        c12_final_closeout_to_route_selected_final_closeout
          (c12_selected_final_closeout_to_closeout boundary.finalRows
            (boundary.selected n hn hodd hgt)) }
def c12_standard_side_boundary_to_selected_route
    (boundary : C12StandardSideStrictDescentBoundary) :
    ∀ n : Nat, 0 < n -> Odd n -> 1 < n -> C12RouteSelectedFinalCloseout n :=
  (c12_standard_side_boundary_to_route_selected_boundary boundary).selectedRoute
theorem c12_c10_iter_one_fixed (k : Nat) :
    c10TOddIter 1 k = 1 := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      simp [c10TOddIter, ih]
      native_decide
theorem c12_row11_a1_standard_route_hits_one :
    c10TOddIter 75 3 = 1 := by
  native_decide
theorem c12_row11_a1_standard_route_stays_one (j : Nat) :
    c10TOddIter 75 (3 + j) = 1 := by
  rw [← c10_iter_append 75 3 j, c12_row11_a1_standard_route_hits_one,
    c12_c10_iter_one_fixed]
theorem c12_row11_a1_stock_target_not_standard_endpoint
    (k : Nat) :
    c10TOddIter 75 k ≠ 7 := by
  by_cases hlt : k < 3
  · interval_cases k <;> native_decide
  · have hk : k = 3 + (k - 3) := by omega
    rw [hk, c12_row11_a1_standard_route_stays_one]
    norm_num

def c15Class21Residue (L : Nat) : Nat :=
  match L % 16 with
  | 0 => 37
  | 1 => 55
  | 2 => 61
  | 3 => 63
  | 4 => 21
  | 5 => 7
  | 6 => 45
  | 7 => 15
  | 8 => 5
  | 9 => 23
  | 10 => 29
  | 11 => 31
  | 12 => 53
  | 13 => 39
  | 14 => 13
  | _ => 47
theorem c15_class21_residue_lt64 (L : Nat) :
    c15Class21Residue L < 64 := by
  unfold c15Class21Residue
  split <;> omega
theorem c15_class21_residue_odd (L : Nat) :
    c15Class21Residue L % 2 = 1 := by
  unfold c15Class21Residue
  split <;> decide
theorem c15_class21_residue_pos (L : Nat) :
    0 < c15Class21Residue L := by
  have hodd := c15_class21_residue_odd L
  omega
theorem c15_class21_residue_defining_mod64 (L : Nat) :
    (3 ^ L * c15Class21Residue L) % 64 = 37 := by
  have hpow : 3 ^ L % 64 = 3 ^ (L % 16) % 64 := by
    have he : Nat.ModEq (2 ^ 4) L (L % 16) := by
      change L % 16 = (L % 16) % 16
      rw [Nat.mod_eq_of_lt (Nat.mod_lt L (by norm_num))]
    have hpowMod := c7_pow3_mod_pow_of_exp_mod 4 L (L % 16) (by norm_num) he
    unfold Nat.ModEq at hpowMod
    norm_num at hpowMod
    exact hpowMod
  have hres : (3 ^ (L % 16) * c15Class21Residue L) % 64 = 37 := by
    have hlt : L % 16 < 16 := Nat.mod_lt L (by norm_num)
    unfold c15Class21Residue
    interval_cases L % 16 <;> native_decide
  have hmul : Nat.ModEq 64 (3 ^ L * c15Class21Residue L)
      (3 ^ (L % 16) * c15Class21Residue L) := by
    exact (Nat.ModEq.mul_right (c15Class21Residue L) (by
      unfold Nat.ModEq
      exact hpow))
  unfold Nat.ModEq at hmul
  rw [hmul, hres]
theorem c15_class21_residue_unique_mod64
    (L c : Nat) (hc : (3 ^ L * c) % 64 = 37) :
    Nat.ModEq 64 c (c15Class21Residue L) := by
  have htarget :
      Nat.ModEq 64 (3 ^ L * c + 0) (3 ^ L * c15Class21Residue L + 0) := by
    unfold Nat.ModEq
    rw [Nat.add_zero, Nat.add_zero, hc, c15_class21_residue_defining_mod64 L]
  exact affine3pow_injective_mod_pow2 L 6 0 c (c15Class21Residue L) htarget
def c15Class21CNext (L u : Nat) : Nat :=
  (3 ^ L * (c15Class21Residue L + 64 * u) - 1) / 4
theorem c15_class21_raw_mod64_of_u (L u : Nat) :
    (3 ^ L * (c15Class21Residue L + 64 * u) - 1) % 64 = 36 := by
  have hmain := c15_class21_residue_defining_mod64 L
  have hmul64 : (3 ^ L * (64 * u)) % 64 = 0 := by
    have hdvd : 64 ∣ 3 ^ L * (64 * u) := by
      refine ⟨3 ^ L * u, ?_⟩
      ring
    exact Nat.dvd_iff_mod_eq_zero.mp hdvd
  have hprod : (3 ^ L * (c15Class21Residue L + 64 * u)) % 64 = 37 := by
    rw [Nat.mul_add, Nat.add_mod, hmain, hmul64]
  have hsub : (3 ^ L * (c15Class21Residue L + 64 * u) - 1) % 64 =
      (37 - 1) % 64 := by
    have hform := Nat.mod_add_div (3 ^ L * (c15Class21Residue L + 64 * u)) 64
    rw [hprod] at hform
    omega
  rw [hsub]
theorem c15_class21_raw_v2_eq_two (L u : Nat) :
    c3V2 (3 ^ L * (c15Class21Residue L + 64 * u) - 1) = 2 := by
  refine c3_v2_eq_of _ 2 ?_ ?_ ?_
  · have hrespos := c15_class21_residue_pos L
    have hprodpos : 1 < 3 ^ L * (c15Class21Residue L + 64 * u) := by
      have hpow : 1 <= 3 ^ L := Nat.succ_le_of_lt (Nat.pow_pos (by omega))
      have hres37 : 5 <= c15Class21Residue L := by
        unfold c15Class21Residue
        split <;> omega
      nlinarith
    omega
  · have hmod := c15_class21_raw_mod64_of_u L u
    exact ⟨(3 ^ L * (c15Class21Residue L + 64 * u) - 1) / 4, by
      have h4 : (3 ^ L * (c15Class21Residue L + 64 * u) - 1) % 4 = 0 := by
        have hmod4 : 36 % 4 = 0 := by norm_num
        have hcoarse : (3 ^ L * (c15Class21Residue L + 64 * u) - 1) % 4 =
            ((3 ^ L * (c15Class21Residue L + 64 * u) - 1) % 64) % 4 := by
          rw [Nat.mod_mod_of_dvd _ (by norm_num : 4 ∣ 64)]
        rw [hcoarse, hmod, hmod4]
      omega⟩
  · intro h8
    obtain ⟨a, ha⟩ := h8
    have hmod := c15_class21_raw_mod64_of_u L u
    have hmod8 : (3 ^ L * (c15Class21Residue L + 64 * u) - 1) % 8 = 0 := by
      rw [ha]
      exact Nat.mul_mod_right _ _
    have hcoarse : (3 ^ L * (c15Class21Residue L + 64 * u) - 1) % 8 =
        ((3 ^ L * (c15Class21Residue L + 64 * u) - 1) % 64) % 8 := by
      rw [Nat.mod_mod_of_dvd _ (by norm_num : 8 ∣ 64)]
    rw [hcoarse, hmod] at hmod8
    norm_num at hmod8
theorem c15_class21_cnext_affine (L u : Nat) :
    c15Class21CNext L u =
      (3 ^ L * c15Class21Residue L - 1) / 4 + 16 * 3 ^ L * u := by
  unfold c15Class21CNext
  have hdiv_const : 4 ∣ 3 ^ L * c15Class21Residue L - 1 := by
    have hmod := c15_class21_residue_defining_mod64 L
    have hmod4 : (3 ^ L * c15Class21Residue L - 1) % 4 = 0 := by
      have hform := Nat.mod_add_div (3 ^ L * c15Class21Residue L) 64
      rw [hmod] at hform
      omega
    exact Nat.dvd_iff_mod_eq_zero.mpr hmod4
  obtain ⟨b, hb⟩ := hdiv_const
  have hbval : (3 ^ L * c15Class21Residue L - 1) / 4 = b := by
    rw [hb, Nat.mul_div_cancel_left b (by omega : 0 < 4)]
  have hraw : 3 ^ L * (c15Class21Residue L + 64 * u) - 1 =
      4 * (b + 16 * 3 ^ L * u) := by
    have hpos : 0 < 3 ^ L * c15Class21Residue L := by
      exact Nat.mul_pos (Nat.pow_pos (by omega)) (c15_class21_residue_pos L)
    rw [Nat.mul_add]
    rw [show 3 ^ L * c15Class21Residue L + 3 ^ L * (64 * u) - 1 =
        (3 ^ L * c15Class21Residue L - 1) + 3 ^ L * (64 * u) by omega]
    rw [hb]
    ring
  rw [hraw, Nat.mul_div_cancel_left _ (by omega : 0 < 4), hbval]
theorem c15_class21_base_divisible_by_four (L : Nat) :
    4 ∣ 3 ^ L * c15Class21Residue L - 1 := by
  have hmod := c15_class21_residue_defining_mod64 L
  have hmod4 : (3 ^ L * c15Class21Residue L - 1) % 4 = 0 := by
    have hform := Nat.mod_add_div (3 ^ L * c15Class21Residue L) 64
    rw [hmod] at hform
    omega
  exact Nat.dvd_iff_mod_eq_zero.mpr hmod4
theorem c15_class21_base_mod16 (L : Nat) :
    ((3 ^ L * c15Class21Residue L - 1) / 4) % 16 = 9 := by
  have hmod := c15_class21_residue_defining_mod64 L
  have hform := Nat.mod_add_div (3 ^ L * c15Class21Residue L) 64
  rw [hmod] at hform
  omega
theorem c15_class21_base_odd (L : Nat) :
    ((3 ^ L * c15Class21Residue L - 1) / 4) % 2 = 1 := by
  have hbase := c15_class21_base_mod16 L
  omega
theorem c15_class21_cnext_mod16 (L u : Nat) :
    c15Class21CNext L u % 16 = 9 := by
  unfold c15Class21CNext
  have hmod := c15_class21_raw_mod64_of_u L u
  have hform := Nat.mod_add_div (3 ^ L * (c15Class21Residue L + 64 * u) - 1) 64
  rw [hmod] at hform
  omega
theorem c15_class21_cnext_period_pow2
    (L k u t : Nat) :
    Nat.ModEq (2 ^ (k + 4))
      (c15Class21CNext L (u + 2 ^ k * t))
      (c15Class21CNext L u) := by
  have hleft :
      c15Class21CNext L (u + 2 ^ k * t) =
        c15Class21CNext L u + 2 ^ (k + 4) * (3 ^ L * t) := by
    rw [c15_class21_cnext_affine L (u + 2 ^ k * t),
      c15_class21_cnext_affine L u]
    rw [Nat.pow_add]
    norm_num
    ring
  rw [hleft]
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm] using
    (Nat.ModEq.modulus_mul_add :
      (2 ^ (k + 4)) * (3 ^ L * t) + c15Class21CNext L u ≡
        c15Class21CNext L u [MOD 2 ^ (k + 4)])
theorem c15_class21_cnext_layer_surjective
    (L k x : Nat) :
    ∃ u, Nat.ModEq (2 ^ (k + 4)) (c15Class21CNext L u)
      ((3 ^ L * c15Class21Residue L - 1) / 4 + 16 * x) := by
  obtain ⟨u, hu⟩ := affine3pow_surjective_mod_pow2 L k 0 x
  refine ⟨u, ?_⟩
  rw [c15_class21_cnext_affine L u]
  have hscaled :
      Nat.ModEq (16 * 2 ^ k) (16 * (3 ^ L * u + 0)) (16 * x) := by
    have hraw : Nat.ModEq (16 * 2 ^ k) (16 * (3 ^ L * u + 0)) (16 * x) :=
      Nat.ModEq.mul_left' 16 hu
    exact hraw
  have hmodulus : 16 * 2 ^ k = 2 ^ (k + 4) := by
    rw [Nat.pow_add]
    norm_num
    ring
  rw [hmodulus] at hscaled
  have hadd := Nat.ModEq.add_left ((3 ^ L * c15Class21Residue L - 1) / 4) hscaled
  simpa [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hadd
theorem c15_class21_cnext_layer_injective
    (L k u v : Nat)
    (h : Nat.ModEq (2 ^ (k + 4))
      (c15Class21CNext L u) (c15Class21CNext L v)) :
    Nat.ModEq (2 ^ k) u v := by
  rw [c15_class21_cnext_affine L u, c15_class21_cnext_affine L v] at h
  have hnorm :
      Nat.ModEq (2 ^ (k + 4))
        ((3 ^ L * c15Class21Residue L - 1) / 4 + 16 * (3 ^ L * u))
        ((3 ^ L * c15Class21Residue L - 1) / 4 + 16 * (3 ^ L * v)) := by
    simpa [Nat.mul_assoc] using h
  have hcancel :
      Nat.ModEq (2 ^ (k + 4)) (16 * (3 ^ L * u)) (16 * (3 ^ L * v)) := by
    exact Nat.ModEq.add_left_cancel' ((3 ^ L * c15Class21Residue L - 1) / 4) hnorm
  have hscaled :
      Nat.ModEq (16 * 2 ^ k) (16 * (3 ^ L * u)) (16 * (3 ^ L * v)) := by
    simpa [Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcancel
  have hinner :
      Nat.ModEq (2 ^ k) (3 ^ L * u) (3 ^ L * v) := by
    exact Nat.ModEq.mul_left_cancel' (by norm_num : 16 ≠ 0) hscaled
  have hwith_zero :
      Nat.ModEq (2 ^ k) (3 ^ L * u + 0) (3 ^ L * v + 0) := by
    simpa using hinner
  exact affine3pow_injective_mod_pow2 L k 0 u v hwith_zero
theorem c15_class21_layer_offset_for_target
    (L k target : Nat) (htarget : target % 16 = 9) :
    ∃ x, Nat.ModEq (2 ^ (k + 4))
      ((3 ^ L * c15Class21Residue L - 1) / 4 + 16 * x) target := by
  let b := (3 ^ L * c15Class21Residue L - 1) / 4
  let m := 2 ^ k
  let r := (b / 16) % m
  let s := (b / 16) / m
  let x := target / 16 + m - r
  refine ⟨x, ?_⟩
  have hmpos : 0 < m := by
    simp [m]
  have hpow : 2 ^ (k + 4) = 16 * m := by
    simp [m, Nat.pow_add]
    ring
  have hbmod : b % 16 = 9 := by
    simpa [b] using c15_class21_base_mod16 L
  have hbform := Nat.mod_add_div b 16
  have htform := Nat.mod_add_div target 16
  rw [hbmod] at hbform
  rw [htarget] at htform
  have hbdiv : r + m * s = b / 16 := by
    simpa [r, s] using Nat.mod_add_div (b / 16) m
  have hinner :
      b / 16 + x = target / 16 + m * (s + 1) := by
    have hle : r <= target / 16 + m := by
      have hlt : r < m := by
        simpa [r] using Nat.mod_lt (b / 16) hmpos
      omega
    calc
      b / 16 + x = (r + m * s) + (target / 16 + m - r) := by
        rw [← hbdiv]
      _ = target / 16 + (m * s + m) := by omega
      _ = target / 16 + m * (s + 1) := by ring
  have hrewrite :
      b + 16 * x =
        target + (16 * m) * (s + 1) := by
    calc
      b + 16 * x = (9 + 16 * (b / 16)) + 16 * x := by rw [hbform]
      _ = 9 + 16 * (b / 16 + x) := by ring
      _ = 9 + 16 * (target / 16 + m * (s + 1)) := by rw [hinner]
      _ = (9 + 16 * (target / 16)) + (16 * m) * (s + 1) := by ring
      _ = target + (16 * m) * (s + 1) := by rw [htform]
  rw [hpow]
  rw [hrewrite]
  simpa [Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (Nat.ModEq.modulus_mul_add :
      (16 * m) * (s + 1) + target ≡ target [MOD 16 * m])
theorem c15_class21_cnext_layer_target_exists_unique
    (L k target : Nat) (htarget : target % 16 = 9) :
    ∃ u, Nat.ModEq (2 ^ (k + 4)) (c15Class21CNext L u) target ∧
      ∀ v, Nat.ModEq (2 ^ (k + 4)) (c15Class21CNext L v) target ->
        Nat.ModEq (2 ^ k) v u := by
  obtain ⟨x, hx⟩ := c15_class21_layer_offset_for_target L k target htarget
  obtain ⟨u, hu⟩ := c15_class21_cnext_layer_surjective L k x
  refine ⟨u, ?_, ?_⟩
  · exact hu.trans hx
  · intro v hv
    exact c15_class21_cnext_layer_injective L k v u (hv.trans (hu.trans hx).symm)
theorem c15_class21_next_length_one (L u : Nat) :
    c3V2 (c15Class21CNext L u + 1) = 1 := by
  refine c3_v2_eq_of _ 1 (by
    have hmod := c15_class21_cnext_mod16 L u
    omega) ?_ ?_
  · have hmod := c15_class21_cnext_mod16 L u
    exact ⟨(c15Class21CNext L u + 1) / 2, by omega⟩
  · intro h4
    have hmod := c15_class21_cnext_mod16 L u
    obtain ⟨a, ha⟩ := h4
    omega
theorem c15_uniform_mod64_entry_to_class9 (L u : Nat) :
    c3V2 (3 ^ L * (c15Class21Residue L + 64 * u) - 1) = 2 ∧
      (3 ^ L * (c15Class21Residue L + 64 * u) - 1) / 4 =
        c15Class21CNext L u ∧
      c3V2 (c15Class21CNext L u + 1) = 1 ∧
      c15Class21CNext L u % 16 = 9 := by
  exact ⟨c15_class21_raw_v2_eq_two L u,
    rfl,
    c15_class21_next_length_one L u,
    c15_class21_cnext_mod16 L u⟩
theorem c15_q5_cnext_u_residue_exists_unique (L : Nat) :
    ∃ u, Nat.ModEq (2 ^ 20) (c15Class21CNext L u) 217 ∧
      ∀ v, Nat.ModEq (2 ^ 20) (c15Class21CNext L v) 217 ->
        Nat.ModEq (2 ^ 16) v u :=
  c15_class21_cnext_layer_target_exists_unique L 16 217 (by norm_num)
theorem c15_q3_cnext_u_residue_exists_unique (L : Nat) :
    ∃ u, Nat.ModEq (2 ^ 26) (c15Class21CNext L u) 57 ∧
      ∀ v, Nat.ModEq (2 ^ 26) (c15Class21CNext L v) 57 ->
        Nat.ModEq (2 ^ 22) v u :=
  c15_class21_cnext_layer_target_exists_unique L 22 57 (by norm_num)
theorem c15_class21_u_refinement_lifts_to_input_class
    (L k u v : Nat) (h : Nat.ModEq (2 ^ k) u v) :
    Nat.ModEq (2 ^ (k + 6))
      (c15Class21Residue L + 64 * u)
      (c15Class21Residue L + 64 * v) := by
  have hscaled :
      Nat.ModEq (64 * 2 ^ k) (64 * u) (64 * v) :=
    Nat.ModEq.mul_left' 64 h
  have hpow :
      Nat.ModEq (2 ^ (k + 6)) (64 * u) (64 * v) := by
    simpa [Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hscaled
  exact Nat.ModEq.add_left (c15Class21Residue L) hpow
theorem c15_q5_branch_refinement_exists_unique (L : Nat) :
    ∃ uStar, Nat.ModEq (2 ^ 20) (c15Class21CNext L uStar) 217 ∧
      ∀ u, Nat.ModEq (2 ^ 20) (c15Class21CNext L u) 217 ->
        Nat.ModEq (2 ^ 22)
          (c15Class21Residue L + 64 * u)
          (c15Class21Residue L + 64 * uStar) := by
  obtain ⟨uStar, huStar, huniq⟩ := c15_q5_cnext_u_residue_exists_unique L
  refine ⟨uStar, huStar, ?_⟩
  intro u hu
  exact c15_class21_u_refinement_lifts_to_input_class L 16 u uStar (huniq u hu)
theorem c15_q3_branch_refinement_exists_unique (L : Nat) :
    ∃ uStar, Nat.ModEq (2 ^ 26) (c15Class21CNext L uStar) 57 ∧
      ∀ u, Nat.ModEq (2 ^ 26) (c15Class21CNext L u) 57 ->
        Nat.ModEq (2 ^ 28)
          (c15Class21Residue L + 64 * u)
          (c15Class21Residue L + 64 * uStar) := by
  obtain ⟨uStar, huStar, huniq⟩ := c15_q3_cnext_u_residue_exists_unique L
  refine ⟨uStar, huStar, ?_⟩
  intro u hu
  exact c15_class21_u_refinement_lifts_to_input_class L 22 u uStar (huniq u hu)
theorem c15_q5_input_cylinder_exists_unique (L : Nat) :
    ∃ d, Nat.ModEq (2 ^ 22) (3 ^ L * d) 869 ∧
      ∀ q, Nat.ModEq (2 ^ 22) (3 ^ L * q) 869 ->
        Nat.ModEq (2 ^ 22) q d := by
  obtain ⟨d, hd, huniq⟩ :=
    fixed_entrance_affine_preimage_single_residue_class L 22 0 869
  refine ⟨d, ?_, ?_⟩
  · simpa using hd
  · intro q hq
    exact huniq q (by simpa using hq)
theorem c15_q3_input_cylinder_exists_unique (L : Nat) :
    ∃ d, Nat.ModEq (2 ^ 28) (3 ^ L * d) 229 ∧
      ∀ q, Nat.ModEq (2 ^ 28) (3 ^ L * q) 229 ->
        Nat.ModEq (2 ^ 28) q d := by
  obtain ⟨d, hd, huniq⟩ :=
    fixed_entrance_affine_preimage_single_residue_class L 28 0 229
  refine ⟨d, ?_, ?_⟩
  · simpa using hd
  · intro q hq
    exact huniq q (by simpa using hq)
noncomputable def c15Q5InputResidue (L : Nat) : Nat :=
  Classical.choose (c15_q5_input_cylinder_exists_unique L)
noncomputable def c15Q3InputResidue (L : Nat) : Nat :=
  Classical.choose (c15_q3_input_cylinder_exists_unique L)
theorem c15_q5_input_residue_spec (L : Nat) :
    Nat.ModEq (2 ^ 22) (3 ^ L * c15Q5InputResidue L) 869 ∧
      ∀ q, Nat.ModEq (2 ^ 22) (3 ^ L * q) 869 ->
        Nat.ModEq (2 ^ 22) q (c15Q5InputResidue L) :=
  Classical.choose_spec (c15_q5_input_cylinder_exists_unique L)
theorem c15_q3_input_residue_spec (L : Nat) :
    Nat.ModEq (2 ^ 28) (3 ^ L * c15Q3InputResidue L) 229 ∧
      ∀ q, Nat.ModEq (2 ^ 28) (3 ^ L * q) 229 ->
        Nat.ModEq (2 ^ 28) q (c15Q3InputResidue L) :=
  Classical.choose_spec (c15_q3_input_cylinder_exists_unique L)
theorem c15_q5_input_residue_L5_mod :
    Nat.ModEq (2 ^ 22) (c15Q5InputResidue 5) 3227719 := by
  exact ((c15_q5_input_residue_spec 5).2 3227719 (by native_decide)).symm
theorem c15_q5_input_residue_L15_mod :
    Nat.ModEq (2 ^ 22) (c15Q5InputResidue 15) 1209711 := by
  exact ((c15_q5_input_residue_spec 15).2 1209711 (by native_decide)).symm
theorem c15_q3_input_residue_L6_mod :
    Nat.ModEq (2 ^ 28) (c15Q3InputResidue 6) 236031725 := by
  exact ((c15_q3_input_residue_spec 6).2 236031725 (by native_decide)).symm
theorem c15_q3_input_residue_L14_mod :
    Nat.ModEq (2 ^ 28) (c15Q3InputResidue 14) 87714253 := by
  exact ((c15_q3_input_residue_spec 14).2 87714253 (by native_decide)).symm
theorem c15_modeq_to_explicit_residue_form
    {M q r : Nat} (hr : r < M) (h : Nat.ModEq M q r) :
    ∃ a, q = M * a + r := by
  unfold Nat.ModEq at h
  have hform := Nat.mod_add_div q M
  rw [h] at hform
  rw [Nat.mod_eq_of_lt hr] at hform
  refine ⟨q / M, ?_⟩
  omega
theorem c15_q5_L5_input_class_explicit_form
    (q : Nat) (hq : Nat.ModEq (2 ^ 22) q (c15Q5InputResidue 5)) :
    ∃ a, q = 2 ^ 22 * a + 3227719 := by
  exact c15_modeq_to_explicit_residue_form (by norm_num : 3227719 < 2 ^ 22)
    (hq.trans c15_q5_input_residue_L5_mod)
theorem c15_q5_L15_input_class_explicit_form
    (q : Nat) (hq : Nat.ModEq (2 ^ 22) q (c15Q5InputResidue 15)) :
    ∃ a, q = 2 ^ 22 * a + 1209711 := by
  exact c15_modeq_to_explicit_residue_form (by norm_num : 1209711 < 2 ^ 22)
    (hq.trans c15_q5_input_residue_L15_mod)
theorem c15_q3_L6_input_class_explicit_form
    (q : Nat) (hq : Nat.ModEq (2 ^ 28) q (c15Q3InputResidue 6)) :
    ∃ a, q = 2 ^ 28 * a + 236031725 := by
  exact c15_modeq_to_explicit_residue_form (by norm_num : 236031725 < 2 ^ 28)
    (hq.trans c15_q3_input_residue_L6_mod)
theorem c15_q3_L14_input_class_explicit_form
    (q : Nat) (hq : Nat.ModEq (2 ^ 28) q (c15Q3InputResidue 14)) :
    ∃ a, q = 2 ^ 28 * a + 87714253 := by
  exact c15_modeq_to_explicit_residue_form (by norm_num : 87714253 < 2 ^ 28)
    (hq.trans c15_q3_input_residue_L14_mod)
theorem c15_q5_input_class_target (L q : Nat)
    (hq : Nat.ModEq (2 ^ 22) q (c15Q5InputResidue L)) :
    Nat.ModEq (2 ^ 22) (3 ^ L * q) 869 := by
  exact (Nat.ModEq.mul_left (3 ^ L) hq).trans (c15_q5_input_residue_spec L).1
theorem c15_q3_input_class_target (L q : Nat)
    (hq : Nat.ModEq (2 ^ 28) q (c15Q3InputResidue L)) :
    Nat.ModEq (2 ^ 28) (3 ^ L * q) 229 := by
  exact (Nat.ModEq.mul_left (3 ^ L) hq).trans (c15_q3_input_residue_spec L).1
theorem c15_q5_target_forces_suffix_residue (L q : Nat)
    (h : Nat.ModEq (2 ^ 22) (3 ^ L * q) 869) :
    ((3 ^ L * q - 1) / 4) % (2 ^ 20) = 217 := by
  unfold Nat.ModEq at h
  norm_num at h
  have hform := Nat.mod_add_div (3 ^ L * q) (2 ^ 22)
  norm_num at hform
  rw [h] at hform
  have hraw : 3 ^ L * q - 1 =
      4 * (217 + 2 ^ 20 * ((3 ^ L * q) / 2 ^ 22)) := by
    omega
  rw [hraw, Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)]
  rw [Nat.add_mod, Nat.mul_mod_right]
  norm_num
theorem c15_q3_target_forces_suffix_residue (L q : Nat)
    (h : Nat.ModEq (2 ^ 28) (3 ^ L * q) 229) :
    ((3 ^ L * q - 1) / 4) % (2 ^ 26) = 57 := by
  unfold Nat.ModEq at h
  norm_num at h
  have hform := Nat.mod_add_div (3 ^ L * q) (2 ^ 28)
  norm_num at hform
  rw [h] at hform
  have hraw : 3 ^ L * q - 1 =
      4 * (57 + 2 ^ 26 * ((3 ^ L * q) / 2 ^ 28)) := by
    omega
  rw [hraw, Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)]
  rw [Nat.add_mod, Nat.mul_mod_right]
  norm_num
theorem c15_q5_input_class_forces_suffix_residue (L q : Nat)
    (hq : Nat.ModEq (2 ^ 22) q (c15Q5InputResidue L)) :
    ((3 ^ L * q - 1) / 4) % (2 ^ 20) = 217 :=
  c15_q5_target_forces_suffix_residue L q (c15_q5_input_class_target L q hq)
theorem c15_q3_input_class_forces_suffix_residue (L q : Nat)
    (hq : Nat.ModEq (2 ^ 28) q (c15Q3InputResidue L)) :
    ((3 ^ L * q - 1) / 4) % (2 ^ 26) = 57 :=
  c15_q3_target_forces_suffix_residue L q (c15_q3_input_class_target L q hq)
theorem c15_three_pow_mod2 (L : Nat) :
    3 ^ L % 2 = 1 := by
  induction L with
  | zero => norm_num
  | succ L ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih]
theorem c15_input_residue_odd_of_target
    {k L target d : Nat} (hk : 1 <= k) (htarget : target % 2 = 1)
    (h : Nat.ModEq (2 ^ k) (3 ^ L * d) target) :
    d % 2 = 1 := by
  have h2 : Nat.ModEq 2 (3 ^ L * d) target :=
    Nat.ModEq.of_dvd (by exact ⟨2 ^ (k - 1), by
      calc
        2 ^ k = 2 ^ ((k - 1) + 1) := by rw [Nat.sub_add_cancel hk]
        _ = 2 ^ (k - 1) * 2 := by rw [pow_succ]
        _ = 2 * 2 ^ (k - 1) := by omega⟩) h
  unfold Nat.ModEq at h2
  have hprod : (3 ^ L * d) % 2 = d % 2 := by
    rw [Nat.mul_mod, c15_three_pow_mod2 L]
    omega
  rw [hprod, htarget] at h2
  exact h2
theorem c15_q5_input_residue_odd (L : Nat) :
    c15Q5InputResidue L % 2 = 1 :=
  c15_input_residue_odd_of_target (by norm_num : 1 <= 22)
    (by norm_num : 869 % 2 = 1) (c15_q5_input_residue_spec L).1
theorem c15_q3_input_residue_odd (L : Nat) :
    c15Q3InputResidue L % 2 = 1 :=
  c15_input_residue_odd_of_target (by norm_num : 1 <= 28)
    (by norm_num : 229 % 2 = 1) (c15_q3_input_residue_spec L).1
noncomputable def c15Q5InputOddResidueClass (L : Nat) : C11OneOddResidueClass where
  exponent := 22
  residue := c15Q5InputResidue L
  residue_odd := c15_q5_input_residue_odd L
noncomputable def c15Q3InputOddResidueClass (L : Nat) : C11OneOddResidueClass where
  exponent := 28
  residue := c15Q3InputResidue L
  residue_odd := c15_q3_input_residue_odd L
structure C15AuditedInputCylinders (L : Nat) where
  q5Class : C11OneOddResidueClass
  q5_exponent : q5Class.exponent = 22
  q5_target :
    Nat.ModEq (2 ^ 22) (3 ^ L * q5Class.residue) 869
  q5_unique :
    ∀ q, Nat.ModEq (2 ^ 22) (3 ^ L * q) 869 ->
      Nat.ModEq (2 ^ 22) q q5Class.residue
  q5_suffix_residue :
    ∀ q, Nat.ModEq (2 ^ 22) q q5Class.residue ->
      ((3 ^ L * q - 1) / 4) % (2 ^ 20) = 217
  q3Class : C11OneOddResidueClass
  q3_exponent : q3Class.exponent = 28
  q3_target :
    Nat.ModEq (2 ^ 28) (3 ^ L * q3Class.residue) 229
  q3_unique :
    ∀ q, Nat.ModEq (2 ^ 28) (3 ^ L * q) 229 ->
      Nat.ModEq (2 ^ 28) q q3Class.residue
  q3_suffix_residue :
    ∀ q, Nat.ModEq (2 ^ 28) q q3Class.residue ->
      ((3 ^ L * q - 1) / 4) % (2 ^ 26) = 57
noncomputable def c15_audited_input_cylinders
    (L : Nat) : C15AuditedInputCylinders L :=
  { q5Class := c15Q5InputOddResidueClass L
    q5_exponent := rfl
    q5_target := (c15_q5_input_residue_spec L).1
    q5_unique := (c15_q5_input_residue_spec L).2
    q5_suffix_residue := c15_q5_input_class_forces_suffix_residue L
    q3Class := c15Q3InputOddResidueClass L
    q3_exponent := rfl
    q3_target := (c15_q3_input_residue_spec L).1
    q3_unique := (c15_q3_input_residue_spec L).2
    q3_suffix_residue := c15_q3_input_class_forces_suffix_residue L }
theorem c15_q5_suffix_state_explicit_form (L q : Nat)
    (hq : Nat.ModEq (2 ^ 22) q (c15Q5InputResidue L)) :
    ∃ a, (3 ^ L * q - 1) / 4 = 2 ^ 20 * a + 217 := by
  have hmod : Nat.ModEq (2 ^ 20) ((3 ^ L * q - 1) / 4) 217 := by
    unfold Nat.ModEq
    exact c15_q5_input_class_forces_suffix_residue L q hq
  exact c15_modeq_to_explicit_residue_form (by norm_num : 217 < 2 ^ 20) hmod
theorem c15_q3_suffix_state_explicit_form (L q : Nat)
    (hq : Nat.ModEq (2 ^ 28) q (c15Q3InputResidue L)) :
    ∃ a, (3 ^ L * q - 1) / 4 = 2 ^ 26 * a + 57 := by
  have hmod : Nat.ModEq (2 ^ 26) ((3 ^ L * q - 1) / 4) 57 := by
    unfold Nat.ModEq
    exact c15_q3_input_class_forces_suffix_residue L q hq
  exact c15_modeq_to_explicit_residue_form (by norm_num : 57 < 2 ^ 26) hmod
structure C15Q3AuditedSuffixContinuation (a : Nat) where
  q3 : Nat
  q3_eq : q3 = 2 ^ 26 * a + 57
  raw3_factorization :
    3 ^ 4 * q3 - 1 = 2 ^ 3 * (679477248 * a + 577)
  q4 : Nat
  q4_eq : q4 = 339738624 * a + 289
  next3_length_one :
    679477248 * a + 577 + 1 = 2 * q4
  q4_odd : q4 % 2 = 1
  raw4_factorization :
    3 * q4 - 1 = 2 * (509607936 * a + 433)
  q5 : Nat
  q5_eq : q5 = 254803968 * a + 217
  next4_length_one :
    509607936 * a + 433 + 1 = 2 * q5
  q5_odd : q5 % 2 = 1
  raw5_factorization :
    3 * q5 - 1 = 2 * (382205952 * a + 325)
  q6 : Nat
  q6_eq : q6 = 191102976 * a + 163
  next5_length_one :
    382205952 * a + 325 + 1 = 2 * q6
  q6_odd : q6 % 2 = 1
  raw6_factorization :
    3 * q6 - 1 = 2 ^ 3 * (71663616 * a + 61)
  q7 : Nat
  q7_eq : q7 = 35831808 * a + 31
  next6_length_one :
    71663616 * a + 61 + 1 = 2 * q7
  q7_odd : q7 % 2 = 1
  raw7_factorization :
    3 * q7 - 1 = 2 ^ 2 * (26873856 * a + 23)
  q8 : Nat
  q8_eq : q8 = 3359232 * a + 3
  next7_length_three :
    26873856 * a + 23 + 1 = 2 ^ 3 * q8
  q8_odd : q8 % 2 = 1
  raw8_factorization :
    3 ^ 3 * q8 - 1 = 2 ^ 4 * (5668704 * a + 5)
  q9 : Nat
  q9_eq : q9 = 2834352 * a + 3
  next8_length_one :
    5668704 * a + 5 + 1 = 2 * q9
  q9_odd : q9 % 2 = 1
  q9_mod16 : q9 % 16 = 3
def c15_q3_audited_suffix_continuation
    (a : Nat) : C15Q3AuditedSuffixContinuation a := by
  refine
    { q3 := 2 ^ 26 * a + 57
      q3_eq := rfl
      raw3_factorization := ?_
      q4 := 339738624 * a + 289
      q4_eq := rfl
      next3_length_one := ?_
      q4_odd := ?_
      raw4_factorization := ?_
      q5 := 254803968 * a + 217
      q5_eq := rfl
      next4_length_one := ?_
      q5_odd := ?_
      raw5_factorization := ?_
      q6 := 191102976 * a + 163
      q6_eq := rfl
      next5_length_one := ?_
      q6_odd := ?_
      raw6_factorization := ?_
      q7 := 35831808 * a + 31
      q7_eq := rfl
      next6_length_one := ?_
      q7_odd := ?_
      raw7_factorization := ?_
      q8 := 3359232 * a + 3
      q8_eq := rfl
      next7_length_three := ?_
      q8_odd := ?_
      raw8_factorization := ?_
      q9 := 2834352 * a + 3
      q9_eq := rfl
      next8_length_one := ?_
      q9_odd := ?_
      q9_mod16 := by
        rw [Nat.add_mod, Nat.mul_mod]
        norm_num }
  · norm_num
    omega
  · omega
  · rw [Nat.add_mod, Nat.mul_mod]
    norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · norm_num
    omega
  · omega
  · rw [Nat.add_mod, Nat.mul_mod]
    norm_num
  · norm_num
    omega
  · omega
  · omega
  · norm_num
    omega
  · omega
  · omega
structure C15Q5AuditedSuffixContinuation (a : Nat) where
  q5 : Nat
  q5_eq : q5 = 2 ^ 20 * a + 217
  raw5_factorization :
    3 * q5 - 1 = 2 * (1572864 * a + 325)
  q6 : Nat
  q6_eq : q6 = 786432 * a + 163
  next5_length_one :
    1572864 * a + 325 + 1 = 2 * q6
  q6_odd : q6 % 2 = 1
  raw6_factorization :
    3 * q6 - 1 = 2 ^ 3 * (294912 * a + 61)
  q7 : Nat
  q7_eq : q7 = 147456 * a + 31
  next6_length_one :
    294912 * a + 61 + 1 = 2 * q7
  q7_odd : q7 % 2 = 1
  raw7_factorization :
    3 * q7 - 1 = 2 ^ 2 * (110592 * a + 23)
  q8 : Nat
  q8_eq : q8 = 13824 * a + 3
  next7_length_three :
    110592 * a + 23 + 1 = 2 ^ 3 * q8
  q8_odd : q8 % 2 = 1
  raw8_factorization :
    3 ^ 3 * q8 - 1 = 2 ^ 4 * (23328 * a + 5)
  q9 : Nat
  q9_eq : q9 = 11664 * a + 3
  next8_length_one :
    23328 * a + 5 + 1 = 2 * q9
  q9_odd : q9 % 2 = 1
  q9_mod16 : q9 % 16 = 3
def c15_q5_audited_suffix_continuation
    (a : Nat) : C15Q5AuditedSuffixContinuation a := by
  refine
    { q5 := 2 ^ 20 * a + 217
      q5_eq := rfl
      raw5_factorization := ?_
      q6 := 786432 * a + 163
      q6_eq := rfl
      next5_length_one := ?_
      q6_odd := ?_
      raw6_factorization := ?_
      q7 := 147456 * a + 31
      q7_eq := rfl
      next6_length_one := ?_
      q7_odd := ?_
      raw7_factorization := ?_
      q8 := 13824 * a + 3
      q8_eq := rfl
      next7_length_three := ?_
      q8_odd := ?_
      raw8_factorization := ?_
      q9 := 11664 * a + 3
      q9_eq := rfl
      next8_length_one := ?_
      q9_odd := ?_
      q9_mod16 := by
        rw [Nat.add_mod, Nat.mul_mod]
        norm_num }
  · omega
  · omega
  · omega
  · norm_num
    omega
  · omega
  · omega
  · norm_num
    omega
  · omega
  · omega
  · norm_num
    omega
  · omega
  · omega
structure C15Q3InputClassAuditedSuffixContinuation (L q : Nat) where
  a : Nat
  cnext_eq : (3 ^ L * q - 1) / 4 = 2 ^ 26 * a + 57
  suffix : C15Q3AuditedSuffixContinuation a
  terminal_mod16 : suffix.q9 % 16 = 3
structure C15Q5InputClassAuditedSuffixContinuation (L q : Nat) where
  a : Nat
  cnext_eq : (3 ^ L * q - 1) / 4 = 2 ^ 20 * a + 217
  suffix : C15Q5AuditedSuffixContinuation a
  terminal_mod16 : suffix.q9 % 16 = 3
noncomputable def c15_q3_input_class_audited_suffix_continuation
    (L q : Nat) (hq : Nat.ModEq (2 ^ 28) q (c15Q3InputResidue L)) :
    C15Q3InputClassAuditedSuffixContinuation L q :=
  let a := Classical.choose (c15_q3_suffix_state_explicit_form L q hq)
  let ha := Classical.choose_spec (c15_q3_suffix_state_explicit_form L q hq)
  let suffix := c15_q3_audited_suffix_continuation a
  ⟨a, ha, suffix, suffix.q9_mod16⟩
noncomputable def c15_q5_input_class_audited_suffix_continuation
    (L q : Nat) (hq : Nat.ModEq (2 ^ 22) q (c15Q5InputResidue L)) :
    C15Q5InputClassAuditedSuffixContinuation L q :=
  let a := Classical.choose (c15_q5_suffix_state_explicit_form L q hq)
  let ha := Classical.choose_spec (c15_q5_suffix_state_explicit_form L q hq)
  let suffix := c15_q5_audited_suffix_continuation a
  ⟨a, ha, suffix, suffix.q9_mod16⟩
structure C15DirectDescentResidueMenu where
  direct11 :
    ∀ a, C12DirectOddCofactorCloseout (64 * a + 11) (6 * a + 1) 32
  direct31 :
    ∀ a, C12DirectOddCofactorCloseout (64 * a + 31) (48 * a + 23) 4
  direct43 :
    ∀ a, C12DirectCofactorBoundCloseout (64 * a + 43) (3 * a + 2) 64
  direct27 :
    ∀ a, C12DirectOddCofactorCloseout (256 * a + 27) (48 * a + 5) 16
  direct739 :
    ∀ a, C12DirectCofactorBoundCloseout (1944 * a + 739) (729 * a + 277) 8
def c15_direct_descent_residue_menu : C15DirectDescentResidueMenu :=
  { direct11 := c12_direct11_closeout
    direct31 := c12_direct31_closeout
    direct43 := c12_direct43_bound_closeout
    direct27 := c12_direct27_closeout
    direct739 := c12_direct739_bound_closeout }
inductive C15DirectDescentMenuTarget (source : Nat) : Prop where
  | row11 (a : Nat) :
      source = 64 * a + 11 ->
      C12DirectOddCofactorCloseout (64 * a + 11) (6 * a + 1) 32 ->
      C15DirectDescentMenuTarget source
  | row31 (a : Nat) :
      source = 64 * a + 31 ->
      C12DirectOddCofactorCloseout (64 * a + 31) (48 * a + 23) 4 ->
      C15DirectDescentMenuTarget source
  | row43 (a : Nat) :
      source = 64 * a + 43 ->
      C12DirectCofactorBoundCloseout (64 * a + 43) (3 * a + 2) 64 ->
      C15DirectDescentMenuTarget source
  | row27 (a : Nat) :
      source = 256 * a + 27 ->
      C12DirectOddCofactorCloseout (256 * a + 27) (48 * a + 5) 16 ->
      C15DirectDescentMenuTarget source
  | row739 (a : Nat) :
      source = 1944 * a + 739 ->
      C12DirectCofactorBoundCloseout (1944 * a + 739) (729 * a + 277) 8 ->
      C15DirectDescentMenuTarget source
inductive C15DirectDescentMenuTargetWithC10Endpoint : Nat -> Prop where
  | row11 (a k : Nat)
      (hend : c10TOddIter (64 * a + 11) k = 6 * a + 1) :
      C15DirectDescentMenuTargetWithC10Endpoint (64 * a + 11)
  | row31 (a k : Nat)
      (hend : c10TOddIter (64 * a + 31) k = 48 * a + 23) :
      C15DirectDescentMenuTargetWithC10Endpoint (64 * a + 31)
  | row43 (a endpoint k : Nat)
      (hend : c10TOddIter (64 * a + 43) k = endpoint)
      (hendpos : 0 < endpoint)
      (hendodd : endpoint % 2 = 1)
      (hle : endpoint <= 3 * a + 2) :
      C15DirectDescentMenuTargetWithC10Endpoint (64 * a + 43)
  | row27 (a k : Nat)
      (hend : c10TOddIter (256 * a + 27) k = 48 * a + 5) :
      C15DirectDescentMenuTargetWithC10Endpoint (256 * a + 27)
  | row739 (a endpoint k : Nat)
      (hend : c10TOddIter (1944 * a + 739) k = endpoint)
      (hendpos : 0 < endpoint)
      (hendodd : endpoint % 2 = 1)
      (hle : endpoint <= 729 * a + 277) :
      C15DirectDescentMenuTargetWithC10Endpoint (1944 * a + 739)
theorem c15_direct_descent_endpoint_to_c12_selected
    {source : Nat}
    (hendpoint : C15DirectDescentMenuTargetWithC10Endpoint source) :
    C12SelectedFinalCloseout source := by
  cases hendpoint with
  | row11 a k hend =>
      let hlift : C12DirectOddEndpointLift (64 * a + 11) (6 * a + 1) 32 k :=
        { cofactorCertificate := c12_direct11_closeout a
          endpoint_witness := hend }
      exact
        ⟨C12FinalCloseoutRow.directDescentResidue,
          c12_final_closeout_rows_complete C12FinalCloseoutRow.directDescentResidue,
          C12SelectedFinalRowCloseout.directOdd hlift⟩
  | row31 a k hend =>
      let hlift : C12DirectOddEndpointLift (64 * a + 31) (48 * a + 23) 4 k :=
        { cofactorCertificate := c12_direct31_closeout a
          endpoint_witness := hend }
      exact
        ⟨C12FinalCloseoutRow.directDescentResidue,
          c12_final_closeout_rows_complete C12FinalCloseoutRow.directDescentResidue,
          C12SelectedFinalRowCloseout.directOdd hlift⟩
  | row43 a endpoint k hend hendpos hendodd hle =>
      let hlift :
          C12DirectBoundEndpointLift (64 * a + 43) (3 * a + 2) 64 endpoint k :=
        { cofactorCertificate := c12_direct43_bound_closeout a
          endpoint_witness := hend
          endpoint_positive := hendpos
          endpoint_odd := hendodd
          endpoint_le_cofactor := hle }
      exact
        ⟨C12FinalCloseoutRow.directDescentResidue,
          c12_final_closeout_rows_complete C12FinalCloseoutRow.directDescentResidue,
          C12SelectedFinalRowCloseout.directBound hlift⟩
  | row27 a k hend =>
      let hlift : C12DirectOddEndpointLift (256 * a + 27) (48 * a + 5) 16 k :=
        { cofactorCertificate := c12_direct27_closeout a
          endpoint_witness := hend }
      exact
        ⟨C12FinalCloseoutRow.directDescentResidue,
          c12_final_closeout_rows_complete C12FinalCloseoutRow.directDescentResidue,
          C12SelectedFinalRowCloseout.directOdd hlift⟩
  | row739 a endpoint k hend hendpos hendodd hle =>
      let hlift :
          C12DirectBoundEndpointLift (1944 * a + 739) (729 * a + 277) 8 endpoint k :=
        { cofactorCertificate := c12_direct739_bound_closeout a
          endpoint_witness := hend
          endpoint_positive := hendpos
          endpoint_odd := hendodd
          endpoint_le_cofactor := hle }
      exact
        ⟨C12FinalCloseoutRow.directDescentResidue,
          c12_final_closeout_rows_complete C12FinalCloseoutRow.directDescentResidue,
          C12SelectedFinalRowCloseout.directBound hlift⟩
theorem c15_direct_descent_endpoint_to_c12_route_selected
    {source : Nat}
    (hendpoint : C15DirectDescentMenuTargetWithC10Endpoint source) :
    C12RouteSelectedFinalCloseout source := by
  cases hendpoint with
  | row11 a k hend =>
      let hlift : C12DirectOddEndpointLift (64 * a + 11) (6 * a + 1) 32 k :=
        { cofactorCertificate := c12_direct11_closeout a
          endpoint_witness := hend }
      exact c12_route_selected_direct_odd hlift
  | row31 a k hend =>
      let hlift : C12DirectOddEndpointLift (64 * a + 31) (48 * a + 23) 4 k :=
        { cofactorCertificate := c12_direct31_closeout a
          endpoint_witness := hend }
      exact c12_route_selected_direct_odd hlift
  | row43 a endpoint k hend hendpos hendodd hle =>
      let hlift :
          C12DirectBoundEndpointLift (64 * a + 43) (3 * a + 2) 64 endpoint k :=
        { cofactorCertificate := c12_direct43_bound_closeout a
          endpoint_witness := hend
          endpoint_positive := hendpos
          endpoint_odd := hendodd
          endpoint_le_cofactor := hle }
      exact c12_route_selected_direct_bound hlift
  | row27 a k hend =>
      let hlift : C12DirectOddEndpointLift (256 * a + 27) (48 * a + 5) 16 k :=
        { cofactorCertificate := c12_direct27_closeout a
          endpoint_witness := hend }
      exact c12_route_selected_direct_odd hlift
  | row739 a endpoint k hend hendpos hendodd hle =>
      let hlift :
          C12DirectBoundEndpointLift (1944 * a + 739) (729 * a + 277) 8 endpoint k :=
        { cofactorCertificate := c12_direct739_bound_closeout a
          endpoint_witness := hend
          endpoint_positive := hendpos
          endpoint_odd := hendodd
          endpoint_le_cofactor := hle }
      exact c12_route_selected_direct_bound hlift
structure C15Q5L5DirectDescent27 (a : Nat) where
  q0 : Nat
  q0_eq : q0 = 2 ^ 22 * a + 3227719
  raw_factorization :
    3 * q0 - 1 = 4 * (3145728 * a + 2420789)
  q1 : Nat
  q1_eq : q1 = 1572864 * a + 1210395
  next_length_one :
    3145728 * a + 2420789 + 1 = 2 * q1
  q1_odd : q1 % 2 = 1
  q1_mod256 : q1 % 256 = 27
  q1_direct_closeout :
    C12DirectOddCofactorCloseout q1 (48 * (6144 * a + 4728) + 5) 16
def c15_q5_L5_direct_descent27
    (a : Nat) : C15Q5L5DirectDescent27 a := by
  refine
    { q0 := 2 ^ 22 * a + 3227719
      q0_eq := rfl
      raw_factorization := ?_
      q1 := 1572864 * a + 1210395
      q1_eq := rfl
      next_length_one := ?_
      q1_odd := ?_
      q1_mod256 := ?_
      q1_direct_closeout := ?_ }
  · norm_num
    omega
  · omega
  · omega
  · omega
  · have hq1 : 1572864 * a + 1210395 = 256 * (6144 * a + 4728) + 27 := by
      omega
    rw [hq1]
    exact c12_direct27_closeout (6144 * a + 4728)
structure C15Q5L15DirectChasePrefix (a : Nat) where
  q0 : Nat
  q0_eq : q0 = 2 ^ 22 * a + 1209711
  raw0_factorization :
    3 * q0 - 1 = 4 * (3145728 * a + 907283)
  q1 : Nat
  q1_eq : q1 = 786432 * a + 226821
  next0_length_two :
    3145728 * a + 907283 + 1 = 4 * q1
  q1_odd : q1 % 2 = 1
  raw1_factorization :
    9 * q1 - 1 = 4 * (1769472 * a + 510347)
  q2 : Nat
  q2_eq : q2 = 442368 * a + 127587
  next1_length_two :
    1769472 * a + 510347 + 1 = 4 * q2
  q2_odd : q2 % 2 = 1
  raw2_factorization :
    9 * q2 - 1 = 2 * (1990656 * a + 574141)
  q3 : Nat
  q3_eq : q3 = 995328 * a + 287071
  next2_length_one :
    1990656 * a + 574141 + 1 = 2 * q3
  q3_odd : q3 % 2 = 1
  q3_mod64 : q3 % 64 = 31
  q3_direct_closeout :
    C12DirectOddCofactorCloseout q3 (48 * (15552 * a + 4485) + 23) 4
def c15_q5_L15_direct_chase_prefix
    (a : Nat) : C15Q5L15DirectChasePrefix a := by
  refine
    { q0 := 2 ^ 22 * a + 1209711
      q0_eq := rfl
      raw0_factorization := ?_
      q1 := 786432 * a + 226821
      q1_eq := rfl
      next0_length_two := ?_
      q1_odd := ?_
      raw1_factorization := ?_
      q2 := 442368 * a + 127587
      q2_eq := rfl
      next1_length_two := ?_
      q2_odd := ?_
      raw2_factorization := ?_
      q3 := 995328 * a + 287071
      q3_eq := rfl
      next2_length_one := ?_
      q3_odd := ?_
      q3_mod64 := ?_
      q3_direct_closeout := ?_ }
  · norm_num
    omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · have hq3 : 995328 * a + 287071 = 64 * (15552 * a + 4485) + 31 := by
      omega
    rw [hq3]
    exact c12_direct31_closeout (15552 * a + 4485)
theorem c15_q5_L15_prefix_terminal_mod64
    (a : Nat) : (995328 * a + 287071) % 64 = 31 := by
  omega
theorem c15_q5_L15_prefix_terminal_direct31_closeout
    (a : Nat) :
    C12DirectOddCofactorCloseout
      (995328 * a + 287071) (48 * (15552 * a + 4485) + 23) 4 := by
  have hq3 : 995328 * a + 287071 = 64 * (15552 * a + 4485) + 31 := by
    omega
  rw [hq3]
  exact c12_direct31_closeout (15552 * a + 4485)
theorem c15_q5_L5_terminal_menu_target
    (a : Nat) : C15DirectDescentMenuTarget (1572864 * a + 1210395) := by
  have hq1 : 1572864 * a + 1210395 = 256 * (6144 * a + 4728) + 27 := by
    omega
  exact C15DirectDescentMenuTarget.row27 (6144 * a + 4728) hq1
    (c12_direct27_closeout (6144 * a + 4728))
theorem c15_q5_L15_terminal_menu_target
    (a : Nat) : C15DirectDescentMenuTarget (995328 * a + 287071) := by
  have hq3 : 995328 * a + 287071 = 64 * (15552 * a + 4485) + 31 := by
    omega
  exact C15DirectDescentMenuTarget.row31 (15552 * a + 4485) hq3
    (c12_direct31_closeout (15552 * a + 4485))
structure C15Q5L5InputClassDirectDescent27 (q : Nat) where
  a : Nat
  q_eq : q = 2 ^ 22 * a + 3227719
  exact : C15Q5L5DirectDescent27 a
  terminalMenuTarget :
    C15DirectDescentMenuTarget (1572864 * a + 1210395)
structure C15Q5L15InputClassDirectChasePrefix (q : Nat) where
  a : Nat
  q_eq : q = 2 ^ 22 * a + 1209711
  exact : C15Q5L15DirectChasePrefix a
  terminalMenuTarget :
    C15DirectDescentMenuTarget (995328 * a + 287071)
noncomputable def c15_q5_L5_input_class_direct_descent27
    (q : Nat) (hq : Nat.ModEq (2 ^ 22) q (c15Q5InputResidue 5)) :
    C15Q5L5InputClassDirectDescent27 q :=
  let a := Classical.choose (c15_q5_L5_input_class_explicit_form q hq)
  let ha := Classical.choose_spec (c15_q5_L5_input_class_explicit_form q hq)
  ⟨a, ha, c15_q5_L5_direct_descent27 a, c15_q5_L5_terminal_menu_target a⟩
noncomputable def c15_q5_L15_input_class_direct_chase_prefix
    (q : Nat) (hq : Nat.ModEq (2 ^ 22) q (c15Q5InputResidue 15)) :
    C15Q5L15InputClassDirectChasePrefix q :=
  let a := Classical.choose (c15_q5_L15_input_class_explicit_form q hq)
  let ha := Classical.choose_spec (c15_q5_L15_input_class_explicit_form q hq)
  ⟨a, ha, c15_q5_L15_direct_chase_prefix a, c15_q5_L15_terminal_menu_target a⟩
structure C15Q3L6DirectDescent43 (a : Nat) where
  q0 : Nat
  q0_eq : q0 = 2 ^ 28 * a + 236031725
  raw0_factorization :
    3 * q0 - 1 = 2 * (402653184 * a + 354047587)
  q1 : Nat
  q1_eq : q1 = 100663296 * a + 88511897
  next0_length_two :
    402653184 * a + 354047587 + 1 = 4 * q1
  raw1_factorization :
    9 * q1 - 1 = 32 * (28311552 * a + 24893971)
  q2 : Nat
  q2_eq : q2 = 7077888 * a + 6223493
  next1_length_two :
    28311552 * a + 24893971 + 1 = 4 * q2
  raw2_factorization :
    9 * q2 - 1 = 4 * (15925248 * a + 14002859)
  q3 : Nat
  q3_eq : q3 = 3981312 * a + 3500715
  next2_length_two :
    15925248 * a + 14002859 + 1 = 4 * q3
  q3_odd : q3 % 2 = 1
  q3_mod64 : q3 % 64 = 43
  q3_direct_closeout :
    C12DirectCofactorBoundCloseout q3 (3 * (62208 * a + 54698) + 2) 64
def c15_q3_L6_direct_descent43
    (a : Nat) : C15Q3L6DirectDescent43 a := by
  refine
    { q0 := 2 ^ 28 * a + 236031725
      q0_eq := rfl
      raw0_factorization := ?_
      q1 := 100663296 * a + 88511897
      q1_eq := rfl
      next0_length_two := ?_
      raw1_factorization := ?_
      q2 := 7077888 * a + 6223493
      q2_eq := rfl
      next1_length_two := ?_
      raw2_factorization := ?_
      q3 := 3981312 * a + 3500715
      q3_eq := rfl
      next2_length_two := ?_
      q3_odd := ?_
      q3_mod64 := ?_
      q3_direct_closeout := ?_ }
  · norm_num
    omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · have hq3 : 3981312 * a + 3500715 = 64 * (62208 * a + 54698) + 43 := by
      omega
    rw [hq3]
    exact c12_direct43_bound_closeout (62208 * a + 54698)
theorem c15_q3_L6_terminal_menu_target
    (a : Nat) : C15DirectDescentMenuTarget (3981312 * a + 3500715) := by
  have hq3 : 3981312 * a + 3500715 = 64 * (62208 * a + 54698) + 43 := by
    omega
  exact C15DirectDescentMenuTarget.row43 (62208 * a + 54698) hq3
    (c12_direct43_bound_closeout (62208 * a + 54698))
structure C15Q3L6InputClassDirectDescent43 (q : Nat) where
  a : Nat
  q_eq : q = 2 ^ 28 * a + 236031725
  exact : C15Q3L6DirectDescent43 a
  terminalMenuTarget :
    C15DirectDescentMenuTarget (3981312 * a + 3500715)
noncomputable def c15_q3_L6_input_class_direct_descent43
    (q : Nat) (hq : Nat.ModEq (2 ^ 28) q (c15Q3InputResidue 6)) :
    C15Q3L6InputClassDirectDescent43 q :=
  let a := Classical.choose (c15_q3_L6_input_class_explicit_form q hq)
  let ha := Classical.choose_spec (c15_q3_L6_input_class_explicit_form q hq)
  ⟨a, ha, c15_q3_L6_direct_descent43 a, c15_q3_L6_terminal_menu_target a⟩
structure C15Q3L14DirectChasePrefix (a : Nat) where
  q0 : Nat
  q0_eq : q0 = 2 ^ 28 * a + 87714253
  raw0_factorization :
    3 * q0 - 1 = 2 * (402653184 * a + 131571379)
  q1 : Nat
  q1_eq : q1 = 100663296 * a + 32892845
  next0_length_two :
    402653184 * a + 131571379 + 1 = 4 * q1
  q1_odd : q1 % 2 = 1
  raw1_factorization :
    9 * q1 - 1 = 4 * (226492416 * a + 74008901)
  q2 : Nat
  q2_eq : q2 = 113246208 * a + 37004451
  next1_length_one :
    226492416 * a + 74008901 + 1 = 2 * q2
  q2_odd : q2 % 2 = 1
  raw2_factorization :
    3 * q2 - 1 = 8 * (42467328 * a + 13876669)
  q3 : Nat
  q3_eq : q3 = 21233664 * a + 6938335
  next2_length_one :
    42467328 * a + 13876669 + 1 = 2 * q3
  q3_odd : q3 % 2 = 1
  raw3_factorization :
    3 * q3 - 1 = 4 * (15925248 * a + 5203751)
  q4 : Nat
  q4_eq : q4 = 1990656 * a + 650469
  next3_length_three :
    15925248 * a + 5203751 + 1 = 8 * q4
  q4_odd : q4 % 2 = 1
  raw4_factorization :
    27 * q4 - 1 = 2 * (26873856 * a + 8781331)
  q5 : Nat
  q5_eq : q5 = 6718464 * a + 2195333
  next4_length_two :
    26873856 * a + 8781331 + 1 = 4 * q5
  q5_odd : q5 % 2 = 1
  raw5_factorization :
    9 * q5 - 1 = 4 * (15116544 * a + 4939499)
  q6 : Nat
  q6_eq : q6 = 3779136 * a + 1234875
  next5_length_two :
    15116544 * a + 4939499 + 1 = 4 * q6
  q6_odd : q6 % 2 = 1
  raw6_factorization :
    9 * q6 - 1 = 2 * (17006112 * a + 5556937)
  q7 : Nat
  q7_eq : q7 = 8503056 * a + 2778469
  next6_length_one :
    17006112 * a + 5556937 + 1 = 2 * q7
  q7_odd : q7 % 2 = 1
def c15_q3_L14_direct_chase_prefix
    (a : Nat) : C15Q3L14DirectChasePrefix a := by
  refine
    { q0 := 2 ^ 28 * a + 87714253
      q0_eq := rfl
      raw0_factorization := ?_
      q1 := 100663296 * a + 32892845
      q1_eq := rfl
      next0_length_two := ?_
      q1_odd := ?_
      raw1_factorization := ?_
      q2 := 113246208 * a + 37004451
      q2_eq := rfl
      next1_length_one := ?_
      q2_odd := ?_
      raw2_factorization := ?_
      q3 := 21233664 * a + 6938335
      q3_eq := rfl
      next2_length_one := ?_
      q3_odd := ?_
      raw3_factorization := ?_
      q4 := 1990656 * a + 650469
      q4_eq := rfl
      next3_length_three := ?_
      q4_odd := ?_
      raw4_factorization := ?_
      q5 := 6718464 * a + 2195333
      q5_eq := rfl
      next4_length_two := ?_
      q5_odd := ?_
      raw5_factorization := ?_
      q6 := 3779136 * a + 1234875
      q6_eq := rfl
      next5_length_two := ?_
      q6_odd := ?_
      raw6_factorization := ?_
      q7 := 8503056 * a + 2778469
      q7_eq := rfl
      next6_length_one := ?_
      q7_odd := ?_ }
  · norm_num
    omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
structure C15Q3L14TailTwoStepCompression (a : Nat) where
  q7 : Nat
  q7_eq : q7 = 8503056 * a + 2778469
  raw7_factorization :
    3 * q7 - 1 = 2 * (12754584 * a + 4167703)
  q8 : Nat
  q8_eq : q8 = 12754584 * a + 4167703
  q8_odd : q8 % 2 = 1
  raw8_factorization :
    3 * q8 - 1 = 4 * (9565938 * a + 3125777)
  q9 : Nat
  q9_eq : q9 = 9565938 * a + 3125777
  q9_odd : q9 % 2 = 1
def c15_q3_L14_tail_two_step_compression
    (a : Nat) : C15Q3L14TailTwoStepCompression a := by
  refine
    { q7 := 8503056 * a + 2778469
      q7_eq := rfl
      raw7_factorization := ?_
      q8 := 12754584 * a + 4167703
      q8_eq := rfl
      q8_odd := ?_
      raw8_factorization := ?_
      q9 := 9565938 * a + 3125777
      q9_eq := rfl
      q9_odd := ?_ }
  · omega
  · omega
  · omega
  · omega
structure C15Q3L14InputClassDirectChasePrefix (q : Nat) where
  a : Nat
  q_eq : q = 2 ^ 28 * a + 87714253
  prefixExact : C15Q3L14DirectChasePrefix a
  tail : C15Q3L14TailTwoStepCompression a
noncomputable def c15_q3_L14_input_class_direct_chase_prefix
    (q : Nat) (hq : Nat.ModEq (2 ^ 28) q (c15Q3InputResidue 14)) :
    C15Q3L14InputClassDirectChasePrefix q :=
  let a := Classical.choose (c15_q3_L14_input_class_explicit_form q hq)
  let ha := Classical.choose_spec (c15_q3_L14_input_class_explicit_form q hq)
  ⟨a, ha, c15_q3_L14_direct_chase_prefix a,
    c15_q3_L14_tail_two_step_compression a⟩
theorem c15_q3_L14_tail_mod64_eq11_of_mod32_eq5
    (a : Nat) (ha : a % 32 = 5) :
    (9565938 * a + 3125777) % 64 = 11 := by
  have hform := Nat.mod_add_div a 32
  rw [ha] at hform
  omega
theorem c15_q3_L14_tail_mod32_eq5_of_mod64_eq11
    (a : Nat) (hq : (9565938 * a + 3125777) % 64 = 11) :
    a % 32 = 5 := by
  have hform := Nat.mod_add_div a 32
  rw [← hform] at hq
  have hlt : a % 32 < 32 := Nat.mod_lt a (by norm_num)
  interval_cases a % 32 <;> omega
theorem c15_q3_L14_tail_mod64_eq11_iff_mod32_eq5
    (a : Nat) :
    (9565938 * a + 3125777) % 64 = 11 ↔ a % 32 = 5 := by
  constructor
  · intro hq
    exact c15_q3_L14_tail_mod32_eq5_of_mod64_eq11 a hq
  · intro ha
    exact c15_q3_L14_tail_mod64_eq11_of_mod32_eq5 a ha
theorem c15_q3_L14_tail_menu_target11_of_mod32_eq5
    (a : Nat) (ha : a % 32 = 5) :
    C15DirectDescentMenuTarget (9565938 * a + 3125777) := by
  have hmod : Nat.ModEq 64 (9565938 * a + 3125777) 11 := by
    unfold Nat.ModEq
    exact c15_q3_L14_tail_mod64_eq11_of_mod32_eq5 a ha
  obtain ⟨k, hk⟩ :=
    c15_modeq_to_explicit_residue_form (by norm_num : 11 < 64) hmod
  exact C15DirectDescentMenuTarget.row11 k hk (c12_direct11_closeout k)
theorem c15_q3_L14_tail_mod64_eq43_of_mod32_eq21
    (a : Nat) (ha : a % 32 = 21) :
    (9565938 * a + 3125777) % 64 = 43 := by
  have hform := Nat.mod_add_div a 32
  rw [ha] at hform
  omega
theorem c15_q3_L14_tail_mod32_eq21_of_mod64_eq43
    (a : Nat) (hq : (9565938 * a + 3125777) % 64 = 43) :
    a % 32 = 21 := by
  have hform := Nat.mod_add_div a 32
  rw [← hform] at hq
  have hlt : a % 32 < 32 := Nat.mod_lt a (by norm_num)
  interval_cases a % 32 <;> omega
theorem c15_q3_L14_tail_mod64_eq43_iff_mod32_eq21
    (a : Nat) :
    (9565938 * a + 3125777) % 64 = 43 ↔ a % 32 = 21 := by
  constructor
  · intro hq
    exact c15_q3_L14_tail_mod32_eq21_of_mod64_eq43 a hq
  · intro ha
    exact c15_q3_L14_tail_mod64_eq43_of_mod32_eq21 a ha
theorem c15_q3_L14_tail_menu_target43_of_mod32_eq21
    (a : Nat) (ha : a % 32 = 21) :
    C15DirectDescentMenuTarget (9565938 * a + 3125777) := by
  have hmod : Nat.ModEq 64 (9565938 * a + 3125777) 43 := by
    unfold Nat.ModEq
    exact c15_q3_L14_tail_mod64_eq43_of_mod32_eq21 a ha
  obtain ⟨k, hk⟩ :=
    c15_modeq_to_explicit_residue_form (by norm_num : 43 < 64) hmod
  exact C15DirectDescentMenuTarget.row43 k hk (c12_direct43_bound_closeout k)
theorem c15_q3_L14_tail_mod256_eq27_of_mod128_eq109
    (a : Nat) (ha : a % 128 = 109) :
    (9565938 * a + 3125777) % 256 = 27 := by
  have hform := Nat.mod_add_div a 128
  rw [ha] at hform
  omega
theorem c15_q3_L14_tail_mod128_eq109_of_mod256_eq27
    (a : Nat) (hq : (9565938 * a + 3125777) % 256 = 27) :
    a % 128 = 109 := by
  have hform := Nat.mod_add_div a 128
  rw [← hform] at hq
  have hlt : a % 128 < 128 := Nat.mod_lt a (by norm_num)
  interval_cases a % 128 <;> omega
theorem c15_q3_L14_tail_mod256_eq27_iff_mod128_eq109
    (a : Nat) :
    (9565938 * a + 3125777) % 256 = 27 ↔ a % 128 = 109 := by
  constructor
  · intro hq
    exact c15_q3_L14_tail_mod128_eq109_of_mod256_eq27 a hq
  · intro ha
    exact c15_q3_L14_tail_mod256_eq27_of_mod128_eq109 a ha
theorem c15_q3_L14_tail_menu_target27_of_mod128_eq109
    (a : Nat) (ha : a % 128 = 109) :
    C15DirectDescentMenuTarget (9565938 * a + 3125777) := by
  have hmod : Nat.ModEq 256 (9565938 * a + 3125777) 27 := by
    unfold Nat.ModEq
    exact c15_q3_L14_tail_mod256_eq27_of_mod128_eq109 a ha
  obtain ⟨k, hk⟩ :=
    c15_modeq_to_explicit_residue_form (by norm_num : 27 < 256) hmod
  exact C15DirectDescentMenuTarget.row27 k hk (c12_direct27_closeout k)
theorem c15_dyadic_parent_iff_children
    (a r M : Nat) (hM : 0 < M) (hr : r < M) :
    a % M = r ↔ a % (2 * M) = r ∨ a % (2 * M) = r + M := by
  constructor
  · intro hparent
    have hdivM : M ∣ 2 * M := by
      refine ⟨2, ?_⟩
      ring
    have hxmod : (a % (2 * M)) % M = r := by
      rw [Nat.mod_mod_of_dvd a hdivM, hparent]
    have hxlt : a % (2 * M) < 2 * M :=
      Nat.mod_lt a (by omega)
    have hquot_lt : (a % (2 * M)) / M < 2 := by
      exact Nat.div_lt_of_lt_mul (by nlinarith [hxlt])
    have hdecomp := Nat.mod_add_div (a % (2 * M)) M
    rw [hxmod] at hdecomp
    interval_cases (a % (2 * M)) / M <;> omega
  · intro hchild
    have hdivM : M ∣ 2 * M := by
      refine ⟨2, ?_⟩
      ring
    have hmod : a % M = (a % (2 * M)) % M := by
      rw [Nat.mod_mod_of_dvd a hdivM]
    rcases hchild with hleft | hright
    · rw [hmod, hleft, Nat.mod_eq_of_lt hr]
    · rw [hmod, hright, Nat.add_mod_right, Nat.mod_eq_of_lt hr]
theorem c15_dyadic_children_disjoint
    (a r M : Nat) (hM : 0 < M) :
    ¬ (a % (2 * M) = r ∧ a % (2 * M) = r + M) := by
  intro h
  have heq : r = r + M := by
    calc
      r = a % (2 * M) := h.left.symm
      _ = r + M := h.right
  omega
structure C15DyadicResidueSplit (M r : Nat) where
  modulus_pos : 0 < M
  residue_lt : r < M
  parent_iff_children :
    ∀ a, a % M = r ↔ a % (2 * M) = r ∨ a % (2 * M) = r + M
  children_disjoint :
    ∀ a, ¬ (a % (2 * M) = r ∧ a % (2 * M) = r + M)
def c15_dyadic_residue_split
    (M r : Nat) (hM : 0 < M) (hr : r < M) :
    C15DyadicResidueSplit M r where
  modulus_pos := hM
  residue_lt := hr
  parent_iff_children := fun a => c15_dyadic_parent_iff_children a r M hM hr
  children_disjoint := fun a => c15_dyadic_children_disjoint a r M hM
structure C15Q3L14Subleaf5Direct11 (b : Nat) where
  q7 : Nat
  q7_eq : q7 = 272097792 * b + 45293749
  raw7_factorization :
    3 * q7 - 1 = 2 * (408146688 * b + 67940623)
  q8 : Nat
  q8_eq : q8 = 408146688 * b + 67940623
  q8_odd : q8 % 2 = 1
  raw8_factorization :
    3 * q8 - 1 = 4 * (306110016 * b + 50955467)
  q9 : Nat
  q9_eq : q9 = 306110016 * b + 50955467
  q9_odd : q9 % 2 = 1
  q9_mod64 : q9 % 64 = 11
  q9_direct_closeout :
    C12DirectOddCofactorCloseout q9 (6 * (4782969 * b + 796179) + 1) 32
def c15_q3_L14_subleaf5_direct11
    (b : Nat) : C15Q3L14Subleaf5Direct11 b := by
  refine
    { q7 := 272097792 * b + 45293749
      q7_eq := rfl
      raw7_factorization := ?_
      q8 := 408146688 * b + 67940623
      q8_eq := rfl
      q8_odd := ?_
      raw8_factorization := ?_
      q9 := 306110016 * b + 50955467
      q9_eq := rfl
      q9_odd := ?_
      q9_mod64 := ?_
      q9_direct_closeout := ?_ }
  · omega
  · omega
  · omega
  · omega
  · omega
  · have hq9 : 306110016 * b + 50955467 = 64 * (4782969 * b + 796179) + 11 := by
      omega
    rw [hq9]
    exact c12_direct11_closeout (4782969 * b + 796179)
structure C15Q3L14Subleaf21Direct43 (b : Nat) where
  q7 : Nat
  q7_eq : q7 = 272097792 * b + 181342645
  raw7_factorization :
    3 * q7 - 1 = 2 * (408146688 * b + 272013967)
  q8 : Nat
  q8_eq : q8 = 408146688 * b + 272013967
  q8_odd : q8 % 2 = 1
  raw8_factorization :
    3 * q8 - 1 = 4 * (306110016 * b + 204010475)
  q9 : Nat
  q9_eq : q9 = 306110016 * b + 204010475
  q9_odd : q9 % 2 = 1
  q9_mod64 : q9 % 64 = 43
  q9_direct_closeout :
    C12DirectCofactorBoundCloseout q9 (3 * (4782969 * b + 3187663) + 2) 64
def c15_q3_L14_subleaf21_direct43
    (b : Nat) : C15Q3L14Subleaf21Direct43 b := by
  refine
    { q7 := 272097792 * b + 181342645
      q7_eq := rfl
      raw7_factorization := ?_
      q8 := 408146688 * b + 272013967
      q8_eq := rfl
      q8_odd := ?_
      raw8_factorization := ?_
      q9 := 306110016 * b + 204010475
      q9_eq := rfl
      q9_odd := ?_
      q9_mod64 := ?_
      q9_direct_closeout := ?_ }
  · omega
  · omega
  · omega
  · omega
  · omega
  · have hq9 : 306110016 * b + 204010475 = 64 * (4782969 * b + 3187663) + 43 := by
      omega
    rw [hq9]
    exact c12_direct43_bound_closeout (4782969 * b + 3187663)
structure C15Q3L14Subleaf109Direct27 (d : Nat) where
  q7 : Nat
  q7_eq : q7 = 1088391168 * d + 929611573
  raw7_factorization :
    3 * q7 - 1 = 2 * (1632586752 * d + 1394417359)
  q8 : Nat
  q8_eq : q8 = 1632586752 * d + 1394417359
  q8_odd : q8 % 2 = 1
  raw8_factorization :
    3 * q8 - 1 = 4 * (1224440064 * d + 1045813019)
  q9 : Nat
  q9_eq : q9 = 1224440064 * d + 1045813019
  q9_odd : q9 % 2 = 1
  q9_mod256 : q9 % 256 = 27
  q9_direct_closeout :
    C12DirectOddCofactorCloseout q9 (48 * (4782969 * d + 4085207) + 5) 16
def c15_q3_L14_subleaf109_direct27
    (d : Nat) : C15Q3L14Subleaf109Direct27 d := by
  refine
    { q7 := 1088391168 * d + 929611573
      q7_eq := rfl
      raw7_factorization := ?_
      q8 := 1632586752 * d + 1394417359
      q8_eq := rfl
      q8_odd := ?_
      raw8_factorization := ?_
      q9 := 1224440064 * d + 1045813019
      q9_eq := rfl
      q9_odd := ?_
      q9_mod256 := ?_
      q9_direct_closeout := ?_ }
  · omega
  · omega
  · omega
  · omega
  · omega
  · have hq9 :
      1224440064 * d + 1045813019 = 256 * (4782969 * d + 4085207) + 27 := by
      omega
    rw [hq9]
    exact c12_direct27_closeout (4782969 * d + 4085207)
theorem c15_q3_L14_subleaf5_menu_target
    (b : Nat) : C15DirectDescentMenuTarget (306110016 * b + 50955467) := by
  have hq9 : 306110016 * b + 50955467 = 64 * (4782969 * b + 796179) + 11 := by
    omega
  exact C15DirectDescentMenuTarget.row11 (4782969 * b + 796179) hq9
    (c12_direct11_closeout (4782969 * b + 796179))
theorem c15_q3_L14_subleaf21_menu_target
    (b : Nat) : C15DirectDescentMenuTarget (306110016 * b + 204010475) := by
  have hq9 : 306110016 * b + 204010475 = 64 * (4782969 * b + 3187663) + 43 := by
    omega
  exact C15DirectDescentMenuTarget.row43 (4782969 * b + 3187663) hq9
    (c12_direct43_bound_closeout (4782969 * b + 3187663))
theorem c15_q3_L14_subleaf109_menu_target
    (d : Nat) : C15DirectDescentMenuTarget (1224440064 * d + 1045813019) := by
  have hq9 :
      1224440064 * d + 1045813019 = 256 * (4782969 * d + 4085207) + 27 := by
    omega
  exact C15DirectDescentMenuTarget.row27 (4782969 * d + 4085207) hq9
    (c12_direct27_closeout (4782969 * d + 4085207))
structure C15Q3L14Subleaf955Direct739 (d : Nat) where
  q7 : Nat
  q7_eq : q7 = 8707129344 * d + 8123196949
  raw7_factorization :
    3 * q7 - 1 = 2 * (13060694016 * d + 12184795423)
  q8 : Nat
  q8_eq : q8 = 13060694016 * d + 12184795423
  q8_odd : q8 % 2 = 1
  raw8_factorization :
    3 * q8 - 1 = 4 * (9795520512 * d + 9138596567)
  q9 : Nat
  q9_eq : q9 = 9795520512 * d + 9138596567
  q9_odd : q9 % 2 = 1
  raw9_factorization :
    3 * q9 - 1 = 4 * (7346640384 * d + 6853947425)
  qA : Nat
  qA_eq : qA = 3673320192 * d + 3426973713
  next9_length_one :
    7346640384 * d + 6853947425 + 1 = 2 * qA
  qA_odd : qA % 2 = 1
  rawA_factorization :
    3 * qA - 1 = 2 * (5509980288 * d + 5140460569)
  qB : Nat
  qB_eq : qB = 2754990144 * d + 2570230285
  nextA_length_one :
    5509980288 * d + 5140460569 + 1 = 2 * qB
  qB_odd : qB % 2 = 1
  rawB_factorization :
    3 * qB - 1 = 2 * (4132485216 * d + 3855345427)
  qStar : Nat
  qStar_eq : qStar = 4132485216 * d + 3855345427
  qStar_odd : qStar % 2 = 1
  qStar_mod1944 : qStar % 1944 = 739
  qStar_direct_closeout :
    C12DirectCofactorBoundCloseout qStar (729 * (2125764 * d + 1983202) + 277) 8
def c15_q3_L14_subleaf955_direct739
    (d : Nat) : C15Q3L14Subleaf955Direct739 d := by
  refine
    { q7 := 8707129344 * d + 8123196949
      q7_eq := rfl
      raw7_factorization := ?_
      q8 := 13060694016 * d + 12184795423
      q8_eq := rfl
      q8_odd := ?_
      raw8_factorization := ?_
      q9 := 9795520512 * d + 9138596567
      q9_eq := rfl
      q9_odd := ?_
      raw9_factorization := ?_
      qA := 3673320192 * d + 3426973713
      qA_eq := rfl
      next9_length_one := ?_
      qA_odd := ?_
      rawA_factorization := ?_
      qB := 2754990144 * d + 2570230285
      qB_eq := rfl
      nextA_length_one := ?_
      qB_odd := ?_
      rawB_factorization := ?_
      qStar := 4132485216 * d + 3855345427
      qStar_eq := rfl
      qStar_odd := ?_
      qStar_mod1944 := ?_
      qStar_direct_closeout := ?_ }
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · have hqStar :
      4132485216 * d + 3855345427 = 1944 * (2125764 * d + 1983202) + 739 := by
      omega
    rw [hqStar]
    exact c12_direct739_bound_closeout (2125764 * d + 1983202)
structure C15Q3L14Subleaf699Direct739 (d : Nat) where
  q7 : Nat
  q7_eq : q7 = 17414258688 * d + 5946414613
  raw7_factorization :
    3 * q7 - 1 = 2 * (26121388032 * d + 8919621919)
  q8 : Nat
  q8_eq : q8 = 26121388032 * d + 8919621919
  q8_odd : q8 % 2 = 1
  raw8_factorization :
    3 * q8 - 1 = 4 * (19591041024 * d + 6689716439)
  q9 : Nat
  q9_eq : q9 = 19591041024 * d + 6689716439
  q9_odd : q9 % 2 = 1
  raw9_factorization :
    3 * q9 - 1 = 4 * (14693280768 * d + 5017287329)
  qA : Nat
  qA_eq : qA = 7346640384 * d + 2508643665
  next9_length_one :
    14693280768 * d + 5017287329 + 1 = 2 * qA
  qA_odd : qA % 2 = 1
  rawA_factorization :
    3 * qA - 1 = 2 * (11019960576 * d + 3762965497)
  qB : Nat
  qB_eq : qB = 5509980288 * d + 1881482749
  nextA_length_one :
    11019960576 * d + 3762965497 + 1 = 2 * qB
  qB_odd : qB % 2 = 1
  rawB_factorization :
    3 * qB - 1 = 2 * (8264970432 * d + 2822224123)
  qStar : Nat
  qStar_eq : qStar = 8264970432 * d + 2822224123
  qStar_odd : qStar % 2 = 1
  qStar_mod1944 : qStar % 1944 = 739
  qStar_direct_closeout :
    C12DirectCofactorBoundCloseout qStar (729 * (4251528 * d + 1451761) + 277) 8
def c15_q3_L14_subleaf699_direct739
    (d : Nat) : C15Q3L14Subleaf699Direct739 d := by
  refine
    { q7 := 17414258688 * d + 5946414613
      q7_eq := rfl
      raw7_factorization := ?_
      q8 := 26121388032 * d + 8919621919
      q8_eq := rfl
      q8_odd := ?_
      raw8_factorization := ?_
      q9 := 19591041024 * d + 6689716439
      q9_eq := rfl
      q9_odd := ?_
      raw9_factorization := ?_
      qA := 7346640384 * d + 2508643665
      qA_eq := rfl
      next9_length_one := ?_
      qA_odd := ?_
      rawA_factorization := ?_
      qB := 5509980288 * d + 1881482749
      qB_eq := rfl
      nextA_length_one := ?_
      qB_odd := ?_
      rawB_factorization := ?_
      qStar := 8264970432 * d + 2822224123
      qStar_eq := rfl
      qStar_odd := ?_
      qStar_mod1944 := ?_
      qStar_direct_closeout := ?_ }
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · have hqStar :
      8264970432 * d + 2822224123 = 1944 * (4251528 * d + 1451761) + 739 := by
      omega
    rw [hqStar]
    exact c12_direct739_bound_closeout (4251528 * d + 1451761)
structure C15Q3L14Subleaf1467Direct739 (d : Nat) where
  q7 : Nat
  q7_eq : q7 = 17414258688 * d + 12476761621
  raw7_factorization :
    3 * q7 - 1 = 2 * (26121388032 * d + 18715142431)
  q8 : Nat
  q8_eq : q8 = 26121388032 * d + 18715142431
  q8_odd : q8 % 2 = 1
  raw8_factorization :
    3 * q8 - 1 = 4 * (19591041024 * d + 14036356823)
  q9 : Nat
  q9_eq : q9 = 19591041024 * d + 14036356823
  q9_odd : q9 % 2 = 1
  raw9_factorization :
    3 * q9 - 1 = 4 * (14693280768 * d + 10527267617)
  qA : Nat
  qA_eq : qA = 7346640384 * d + 5263633809
  next9_length_one :
    14693280768 * d + 10527267617 + 1 = 2 * qA
  qA_odd : qA % 2 = 1
  rawA_factorization :
    3 * qA - 1 = 2 * (11019960576 * d + 7895450713)
  qB : Nat
  qB_eq : qB = 5509980288 * d + 3947725357
  nextA_length_one :
    11019960576 * d + 7895450713 + 1 = 2 * qB
  qB_odd : qB % 2 = 1
  rawB_factorization :
    3 * qB - 1 = 2 * (8264970432 * d + 5921588035)
  qStar : Nat
  qStar_eq : qStar = 8264970432 * d + 5921588035
  qStar_odd : qStar % 2 = 1
  qStar_mod1944 : qStar % 1944 = 739
  qStar_direct_closeout :
    C12DirectCofactorBoundCloseout qStar (729 * (4251528 * d + 3046084) + 277) 8
def c15_q3_L14_subleaf1467_direct739
    (d : Nat) : C15Q3L14Subleaf1467Direct739 d := by
  refine
    { q7 := 17414258688 * d + 12476761621
      q7_eq := rfl
      raw7_factorization := ?_
      q8 := 26121388032 * d + 18715142431
      q8_eq := rfl
      q8_odd := ?_
      raw8_factorization := ?_
      q9 := 19591041024 * d + 14036356823
      q9_eq := rfl
      q9_odd := ?_
      raw9_factorization := ?_
      qA := 7346640384 * d + 5263633809
      qA_eq := rfl
      next9_length_one := ?_
      qA_odd := ?_
      rawA_factorization := ?_
      qB := 5509980288 * d + 3947725357
      qB_eq := rfl
      nextA_length_one := ?_
      qB_odd := ?_
      rawB_factorization := ?_
      qStar := 8264970432 * d + 5921588035
      qStar_eq := rfl
      qStar_odd := ?_
      qStar_mod1944 := ?_
      qStar_direct_closeout := ?_ }
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · have hqStar :
      8264970432 * d + 5921588035 = 1944 * (4251528 * d + 3046084) + 739 := by
      omega
    rw [hqStar]
    exact c12_direct739_bound_closeout (4251528 * d + 3046084)
theorem c15_q3_L14_subleaf955_menu_target
    (d : Nat) : C15DirectDescentMenuTarget (4132485216 * d + 3855345427) := by
  have hqStar :
      4132485216 * d + 3855345427 = 1944 * (2125764 * d + 1983202) + 739 := by
    omega
  exact C15DirectDescentMenuTarget.row739 (2125764 * d + 1983202) hqStar
    (c12_direct739_bound_closeout (2125764 * d + 1983202))
theorem c15_q3_L14_subleaf699_menu_target
    (d : Nat) : C15DirectDescentMenuTarget (8264970432 * d + 2822224123) := by
  have hqStar :
      8264970432 * d + 2822224123 = 1944 * (4251528 * d + 1451761) + 739 := by
    omega
  exact C15DirectDescentMenuTarget.row739 (4251528 * d + 1451761) hqStar
    (c12_direct739_bound_closeout (4251528 * d + 1451761))
theorem c15_q3_L14_subleaf1467_menu_target
    (d : Nat) : C15DirectDescentMenuTarget (8264970432 * d + 5921588035) := by
  have hqStar :
      8264970432 * d + 5921588035 = 1944 * (4251528 * d + 3046084) + 739 := by
    omega
  exact C15DirectDescentMenuTarget.row739 (4251528 * d + 3046084) hqStar
    (c12_direct739_bound_closeout (4251528 * d + 3046084))
theorem c15_q3_L14_subleaf955_menu_target_of_mod1024
    (a : Nat) (ha : a % 1024 = 955) :
    ∃ d, a = 1024 * d + 955 ∧
      C15DirectDescentMenuTarget (4132485216 * d + 3855345427) := by
  have hmod : Nat.ModEq 1024 a 955 := by
    unfold Nat.ModEq
    exact ha
  obtain ⟨d, hd⟩ :=
    c15_modeq_to_explicit_residue_form (by norm_num : 955 < 1024) hmod
  exact ⟨d, hd, c15_q3_L14_subleaf955_menu_target d⟩
theorem c15_q3_L14_subleaf699_menu_target_of_mod2048
    (a : Nat) (ha : a % 2048 = 699) :
    ∃ d, a = 2048 * d + 699 ∧
      C15DirectDescentMenuTarget (8264970432 * d + 2822224123) := by
  have hmod : Nat.ModEq 2048 a 699 := by
    unfold Nat.ModEq
    exact ha
  obtain ⟨d, hd⟩ :=
    c15_modeq_to_explicit_residue_form (by norm_num : 699 < 2048) hmod
  exact ⟨d, hd, c15_q3_L14_subleaf699_menu_target d⟩
theorem c15_q3_L14_subleaf1467_menu_target_of_mod2048
    (a : Nat) (ha : a % 2048 = 1467) :
    ∃ d, a = 2048 * d + 1467 ∧
      C15DirectDescentMenuTarget (8264970432 * d + 5921588035) := by
  have hmod : Nat.ModEq 2048 a 1467 := by
    unfold Nat.ModEq
    exact ha
  obtain ⟨d, hd⟩ :=
    c15_modeq_to_explicit_residue_form (by norm_num : 1467 < 2048) hmod
  exact ⟨d, hd, c15_q3_L14_subleaf1467_menu_target d⟩
structure C15ResidualRepresentativeLandingPackage where
  directMenu : C15DirectDescentResidueMenu
  q5_L5_input_class :
    ∀ q, Nat.ModEq (2 ^ 22) q (c15Q5InputResidue 5) ->
      C15Q5L5InputClassDirectDescent27 q
  q5_L5_exact :
    ∀ a, C15Q5L5DirectDescent27 a
  q5_L5_terminal_direct27 :
    ∀ a, C12DirectOddCofactorCloseout
      (1572864 * a + 1210395) (48 * (6144 * a + 4728) + 5) 16
  q5_L5_menu_target :
    ∀ a, C15DirectDescentMenuTarget (1572864 * a + 1210395)
  q5_L15_input_class :
    ∀ q, Nat.ModEq (2 ^ 22) q (c15Q5InputResidue 15) ->
      C15Q5L15InputClassDirectChasePrefix q
  q5_L15_exact :
    ∀ a, C15Q5L15DirectChasePrefix a
  q5_L15_terminal_direct31 :
    ∀ a, C12DirectOddCofactorCloseout
      (995328 * a + 287071) (48 * (15552 * a + 4485) + 23) 4
  q5_L15_menu_target :
    ∀ a, C15DirectDescentMenuTarget (995328 * a + 287071)
  q3_L6_input_class :
    ∀ q, Nat.ModEq (2 ^ 28) q (c15Q3InputResidue 6) ->
      C15Q3L6InputClassDirectDescent43 q
  q3_L6_exact :
    ∀ a, C15Q3L6DirectDescent43 a
  q3_L6_terminal_direct43 :
    ∀ a, C12DirectCofactorBoundCloseout
      (3981312 * a + 3500715) (3 * (62208 * a + 54698) + 2) 64
  q3_L6_menu_target :
    ∀ a, C15DirectDescentMenuTarget (3981312 * a + 3500715)
  q3_L14_input_class :
    ∀ q, Nat.ModEq (2 ^ 28) q (c15Q3InputResidue 14) ->
      C15Q3L14InputClassDirectChasePrefix q
  q3_L14_prefix :
    ∀ a, C15Q3L14DirectChasePrefix a
  q3_L14_tail :
    ∀ a, C15Q3L14TailTwoStepCompression a
  q3_L14_tail_11_iff :
    ∀ a, (9565938 * a + 3125777) % 64 = 11 ↔ a % 32 = 5
  q3_L14_tail_11_menu_target :
    ∀ a, a % 32 = 5 -> C15DirectDescentMenuTarget (9565938 * a + 3125777)
  q3_L14_tail_43_iff :
    ∀ a, (9565938 * a + 3125777) % 64 = 43 ↔ a % 32 = 21
  q3_L14_tail_43_menu_target :
    ∀ a, a % 32 = 21 -> C15DirectDescentMenuTarget (9565938 * a + 3125777)
  q3_L14_tail_27_iff :
    ∀ a, (9565938 * a + 3125777) % 256 = 27 ↔ a % 128 = 109
  q3_L14_tail_27_menu_target :
    ∀ a, a % 128 = 109 -> C15DirectDescentMenuTarget (9565938 * a + 3125777)
  dyadicSplit :
    ∀ M r, 0 < M -> r < M -> C15DyadicResidueSplit M r
  q3_L14_subleaf5_exact :
    ∀ b, C15Q3L14Subleaf5Direct11 b
  q3_L14_subleaf5_terminal_direct11 :
    ∀ b, C12DirectOddCofactorCloseout
      (306110016 * b + 50955467) (6 * (4782969 * b + 796179) + 1) 32
  q3_L14_subleaf5_menu_target :
    ∀ b, C15DirectDescentMenuTarget (306110016 * b + 50955467)
  q3_L14_subleaf21_exact :
    ∀ b, C15Q3L14Subleaf21Direct43 b
  q3_L14_subleaf21_terminal_direct43 :
    ∀ b, C12DirectCofactorBoundCloseout
      (306110016 * b + 204010475) (3 * (4782969 * b + 3187663) + 2) 64
  q3_L14_subleaf21_menu_target :
    ∀ b, C15DirectDescentMenuTarget (306110016 * b + 204010475)
  q3_L14_subleaf109_exact :
    ∀ d, C15Q3L14Subleaf109Direct27 d
  q3_L14_subleaf109_terminal_direct27 :
    ∀ d, C12DirectOddCofactorCloseout
      (1224440064 * d + 1045813019) (48 * (4782969 * d + 4085207) + 5) 16
  q3_L14_subleaf109_menu_target :
    ∀ d, C15DirectDescentMenuTarget (1224440064 * d + 1045813019)
  q3_L14_subleaf955_exact :
    ∀ d, C15Q3L14Subleaf955Direct739 d
  q3_L14_subleaf955_terminal_direct739 :
    ∀ d, C12DirectCofactorBoundCloseout
      (4132485216 * d + 3855345427) (729 * (2125764 * d + 1983202) + 277) 8
  q3_L14_subleaf955_menu_target :
    ∀ d, C15DirectDescentMenuTarget (4132485216 * d + 3855345427)
  q3_L14_subleaf699_exact :
    ∀ d, C15Q3L14Subleaf699Direct739 d
  q3_L14_subleaf699_terminal_direct739 :
    ∀ d, C12DirectCofactorBoundCloseout
      (8264970432 * d + 2822224123) (729 * (4251528 * d + 1451761) + 277) 8
  q3_L14_subleaf699_menu_target :
    ∀ d, C15DirectDescentMenuTarget (8264970432 * d + 2822224123)
  q3_L14_subleaf1467_exact :
    ∀ d, C15Q3L14Subleaf1467Direct739 d
  q3_L14_subleaf1467_terminal_direct739 :
    ∀ d, C12DirectCofactorBoundCloseout
      (8264970432 * d + 5921588035) (729 * (4251528 * d + 3046084) + 277) 8
  q3_L14_subleaf1467_menu_target :
    ∀ d, C15DirectDescentMenuTarget (8264970432 * d + 5921588035)
  q3_L14_subleaf955_menu_target_of_mod1024 :
    ∀ a, a % 1024 = 955 ->
      ∃ d, a = 1024 * d + 955 ∧
        C15DirectDescentMenuTarget (4132485216 * d + 3855345427)
  q3_L14_subleaf699_menu_target_of_mod2048 :
    ∀ a, a % 2048 = 699 ->
      ∃ d, a = 2048 * d + 699 ∧
        C15DirectDescentMenuTarget (8264970432 * d + 2822224123)
  q3_L14_subleaf1467_menu_target_of_mod2048 :
    ∀ a, a % 2048 = 1467 ->
      ∃ d, a = 2048 * d + 1467 ∧
        C15DirectDescentMenuTarget (8264970432 * d + 5921588035)
structure C15Q3L14HybridDirectDescentTailCompression where
  tail :
    ∀ a, C15Q3L14TailTwoStepCompression a
  tail_11_iff :
    ∀ a, (9565938 * a + 3125777) % 64 = 11 ↔ a % 32 = 5
  tail_11_menu_target :
    ∀ a, a % 32 = 5 -> C15DirectDescentMenuTarget (9565938 * a + 3125777)
  tail_43_iff :
    ∀ a, (9565938 * a + 3125777) % 64 = 43 ↔ a % 32 = 21
  tail_43_menu_target :
    ∀ a, a % 32 = 21 -> C15DirectDescentMenuTarget (9565938 * a + 3125777)
  tail_27_iff :
    ∀ a, (9565938 * a + 3125777) % 256 = 27 ↔ a % 128 = 109
  tail_27_menu_target :
    ∀ a, a % 128 = 109 -> C15DirectDescentMenuTarget (9565938 * a + 3125777)
  subleaf955_menu_target_of_mod1024 :
    ∀ a, a % 1024 = 955 ->
      ∃ d, a = 1024 * d + 955 ∧
        C15DirectDescentMenuTarget (4132485216 * d + 3855345427)
  subleaf699_menu_target_of_mod2048 :
    ∀ a, a % 2048 = 699 ->
      ∃ d, a = 2048 * d + 699 ∧
        C15DirectDescentMenuTarget (8264970432 * d + 2822224123)
  subleaf1467_menu_target_of_mod2048 :
    ∀ a, a % 2048 = 1467 ->
      ∃ d, a = 2048 * d + 1467 ∧
        C15DirectDescentMenuTarget (8264970432 * d + 5921588035)
def c15_q3_L14_hybrid_direct_descent_tail_compression_of
    (P : C15ResidualRepresentativeLandingPackage) :
    C15Q3L14HybridDirectDescentTailCompression where
  tail := P.q3_L14_tail
  tail_11_iff := P.q3_L14_tail_11_iff
  tail_11_menu_target := P.q3_L14_tail_11_menu_target
  tail_43_iff := P.q3_L14_tail_43_iff
  tail_43_menu_target := P.q3_L14_tail_43_menu_target
  tail_27_iff := P.q3_L14_tail_27_iff
  tail_27_menu_target := P.q3_L14_tail_27_menu_target
  subleaf955_menu_target_of_mod1024 := P.q3_L14_subleaf955_menu_target_of_mod1024
  subleaf699_menu_target_of_mod2048 := P.q3_L14_subleaf699_menu_target_of_mod2048
  subleaf1467_menu_target_of_mod2048 := P.q3_L14_subleaf1467_menu_target_of_mod2048
noncomputable def c15_residual_representative_landing_package :
    C15ResidualRepresentativeLandingPackage where
  directMenu := c15_direct_descent_residue_menu
  q5_L5_input_class := c15_q5_L5_input_class_direct_descent27
  q5_L5_exact := c15_q5_L5_direct_descent27
  q5_L5_terminal_direct27 := fun a =>
    (c15_q5_L5_direct_descent27 a).q1_direct_closeout
  q5_L5_menu_target := c15_q5_L5_terminal_menu_target
  q5_L15_input_class := c15_q5_L15_input_class_direct_chase_prefix
  q5_L15_exact := c15_q5_L15_direct_chase_prefix
  q5_L15_terminal_direct31 := c15_q5_L15_prefix_terminal_direct31_closeout
  q5_L15_menu_target := c15_q5_L15_terminal_menu_target
  q3_L6_input_class := c15_q3_L6_input_class_direct_descent43
  q3_L6_exact := c15_q3_L6_direct_descent43
  q3_L6_terminal_direct43 := fun a =>
    (c15_q3_L6_direct_descent43 a).q3_direct_closeout
  q3_L6_menu_target := c15_q3_L6_terminal_menu_target
  q3_L14_input_class := c15_q3_L14_input_class_direct_chase_prefix
  q3_L14_prefix := c15_q3_L14_direct_chase_prefix
  q3_L14_tail := c15_q3_L14_tail_two_step_compression
  q3_L14_tail_11_iff := c15_q3_L14_tail_mod64_eq11_iff_mod32_eq5
  q3_L14_tail_11_menu_target := c15_q3_L14_tail_menu_target11_of_mod32_eq5
  q3_L14_tail_43_iff := c15_q3_L14_tail_mod64_eq43_iff_mod32_eq21
  q3_L14_tail_43_menu_target := c15_q3_L14_tail_menu_target43_of_mod32_eq21
  q3_L14_tail_27_iff := c15_q3_L14_tail_mod256_eq27_iff_mod128_eq109
  q3_L14_tail_27_menu_target := c15_q3_L14_tail_menu_target27_of_mod128_eq109
  dyadicSplit := c15_dyadic_residue_split
  q3_L14_subleaf5_exact := c15_q3_L14_subleaf5_direct11
  q3_L14_subleaf5_terminal_direct11 := fun b =>
    (c15_q3_L14_subleaf5_direct11 b).q9_direct_closeout
  q3_L14_subleaf5_menu_target := c15_q3_L14_subleaf5_menu_target
  q3_L14_subleaf21_exact := c15_q3_L14_subleaf21_direct43
  q3_L14_subleaf21_terminal_direct43 := fun b =>
    (c15_q3_L14_subleaf21_direct43 b).q9_direct_closeout
  q3_L14_subleaf21_menu_target := c15_q3_L14_subleaf21_menu_target
  q3_L14_subleaf109_exact := c15_q3_L14_subleaf109_direct27
  q3_L14_subleaf109_terminal_direct27 := fun d =>
    (c15_q3_L14_subleaf109_direct27 d).q9_direct_closeout
  q3_L14_subleaf109_menu_target := c15_q3_L14_subleaf109_menu_target
  q3_L14_subleaf955_exact := c15_q3_L14_subleaf955_direct739
  q3_L14_subleaf955_terminal_direct739 := fun d =>
    (c15_q3_L14_subleaf955_direct739 d).qStar_direct_closeout
  q3_L14_subleaf955_menu_target := c15_q3_L14_subleaf955_menu_target
  q3_L14_subleaf699_exact := c15_q3_L14_subleaf699_direct739
  q3_L14_subleaf699_terminal_direct739 := fun d =>
    (c15_q3_L14_subleaf699_direct739 d).qStar_direct_closeout
  q3_L14_subleaf699_menu_target := c15_q3_L14_subleaf699_menu_target
  q3_L14_subleaf1467_exact := c15_q3_L14_subleaf1467_direct739
  q3_L14_subleaf1467_terminal_direct739 := fun d =>
    (c15_q3_L14_subleaf1467_direct739 d).qStar_direct_closeout
  q3_L14_subleaf1467_menu_target := c15_q3_L14_subleaf1467_menu_target
  q3_L14_subleaf955_menu_target_of_mod1024 :=
    c15_q3_L14_subleaf955_menu_target_of_mod1024
  q3_L14_subleaf699_menu_target_of_mod2048 :=
    c15_q3_L14_subleaf699_menu_target_of_mod2048
  q3_L14_subleaf1467_menu_target_of_mod2048 :=
    c15_q3_L14_subleaf1467_menu_target_of_mod2048
noncomputable def c15_q3_L14_hybrid_direct_descent_tail_compression :
    C15Q3L14HybridDirectDescentTailCompression :=
  c15_q3_L14_hybrid_direct_descent_tail_compression_of
    c15_residual_representative_landing_package
inductive C15AuditedPullback where
  | q5
  | q3
  deriving DecidableEq
def c15AcceptedBaseTemplateQ1 (u : Nat) : Nat :=
  1 + 6 * u
def c15AcceptedBaseTemplateQ (u : Nat) : Nat :=
  3 + 6 * u
def c15IsAcceptedBaseTemplate (Q : Nat) : Prop :=
  (∃ u, Q = c15AcceptedBaseTemplateQ1 u) ∨
    (∃ u, Q = c15AcceptedBaseTemplateQ u)
def c15AcceptedBaseTemplateC17LedgerRow : C17GlobalEntryLedgerRow :=
  { row := C17Lemma1aGlobalEntryRow.baseTemplates
    conditionKind := C17GlobalEntryConditionKind.baseTemplateFamily
    closeoutType := C17GlobalEntryCloseoutType.fixedEntryFamily }
theorem c15_accepted_base_template_form (u : Nat) :
    c15IsAcceptedBaseTemplate (c15AcceptedBaseTemplateQ u) :=
  Or.inr ⟨u, rfl⟩
theorem c15_accepted_base_template_form_q1 (u : Nat) :
    c15IsAcceptedBaseTemplate (c15AcceptedBaseTemplateQ1 u) :=
  Or.inl ⟨u, rfl⟩
structure C15AcceptedBaseTemplateBoundary (Q : Nat) : Prop where
  accepted : c15IsAcceptedBaseTemplate Q
  c17Row_in_menu :
    C17Lemma1aGlobalEntryRow.baseTemplates ∈ c17Lemma1aGlobalEntryRows
  inputARole :
    C17Lemma1aGlobalEntryRow.baseTemplates.inputARole =
      C17Lemma1aInputARole.fixedEntry
  ledgerRow_in_c17 :
    c15AcceptedBaseTemplateC17LedgerRow ∈ c17GlobalEntryLedgerRows
  ledgerRow_role_agrees :
    C17GlobalEntryLedgerRow.RoleAgrees c15AcceptedBaseTemplateC17LedgerRow
theorem c15_accepted_base_template_boundary (u : Nat) :
    C15AcceptedBaseTemplateBoundary (c15AcceptedBaseTemplateQ u) := by
  refine
    { accepted := c15_accepted_base_template_form u
      c17Row_in_menu := ?_
      inputARole := ?_
      ledgerRow_in_c17 := ?_
      ledgerRow_role_agrees := ?_ }
  · exact c17_lemma1a_global_entry_rows_complete C17Lemma1aGlobalEntryRow.baseTemplates
  · rfl
  · native_decide
  · exact c17_global_entry_ledger_rows_role_agree
      c15AcceptedBaseTemplateC17LedgerRow (by native_decide)
theorem c15_accepted_base_template_boundary_q1 (u : Nat) :
    C15AcceptedBaseTemplateBoundary (c15AcceptedBaseTemplateQ1 u) := by
  refine
    { accepted := c15_accepted_base_template_form_q1 u
      c17Row_in_menu := ?_
      inputARole := ?_
      ledgerRow_in_c17 := ?_
      ledgerRow_role_agrees := ?_ }
  · exact c17_lemma1a_global_entry_rows_complete C17Lemma1aGlobalEntryRow.baseTemplates
  · rfl
  · native_decide
  · exact c17_global_entry_ledger_rows_role_agree
      c15AcceptedBaseTemplateC17LedgerRow (by native_decide)
def c15Q5ResidualLMod16 (r : Nat) : Prop :=
  r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 11 ∨ r = 15
def c15Q3ResidualLMod16 (r : Nat) : Prop :=
  r = 3 ∨ r = 6 ∨ r = 14
def c15Q5BaseTemplateLMod16 (r : Nat) : Prop :=
  r = 3 ∨ r = 7 ∨ r = 11
def c15Q3BaseTemplateLMod16 (r : Nat) : Prop :=
  r = 3
def c15Q5DirectChaseLMod16 (r : Nat) : Prop :=
  r = 5 ∨ r = 15
def c15Q3DirectChaseLMod16 (r : Nat) : Prop :=
  r = 6 ∨ r = 14
theorem c15_q5_ledger_row_covers_residual_class (r : Nat)
    (h : c15Q5ResidualLMod16 r) :
    c15Q5BaseTemplateLMod16 r ∨ c15Q5DirectChaseLMod16 r := by
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (Or.inl rfl)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl (Or.inr (Or.inl rfl))
  · exact Or.inl (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inr rfl)
theorem c15_q3_ledger_row_covers_residual_class (r : Nat)
    (h : c15Q3ResidualLMod16 r) :
    c15Q3BaseTemplateLMod16 r ∨ c15Q3DirectChaseLMod16 r := by
  rcases h with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
theorem c15_q5_base_template_row_is_residual (r : Nat)
    (h : c15Q5BaseTemplateLMod16 r) : c15Q5ResidualLMod16 r := by
  rcases h with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
theorem c15_q3_base_template_row_is_residual (r : Nat)
    (h : c15Q3BaseTemplateLMod16 r) : c15Q3ResidualLMod16 r := by
  exact Or.inl h
theorem c15_q5_direct_chase_row_is_residual (r : Nat)
    (h : c15Q5DirectChaseLMod16 r) : c15Q5ResidualLMod16 r := by
  rcases h with rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
theorem c15_q3_direct_chase_row_is_residual (r : Nat)
    (h : c15Q3DirectChaseLMod16 r) : c15Q3ResidualLMod16 r := by
  rcases h with rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
theorem c15_q5_base_template_row_boundary
    (r u : Nat) (h : c15Q5BaseTemplateLMod16 r) :
    c15Q5ResidualLMod16 r ∧
      C15AcceptedBaseTemplateBoundary (c15AcceptedBaseTemplateQ u) := by
  exact ⟨c15_q5_base_template_row_is_residual r h,
    c15_accepted_base_template_boundary u⟩
theorem c15_q3_base_template_row_boundary
    (r u : Nat) (h : c15Q3BaseTemplateLMod16 r) :
    c15Q3ResidualLMod16 r ∧
      C15AcceptedBaseTemplateBoundary (c15AcceptedBaseTemplateQ u) := by
  exact ⟨c15_q3_base_template_row_is_residual r h,
    c15_accepted_base_template_boundary u⟩
inductive C15ResidualLaunchRowOutcome :
    C15AuditedPullback -> Nat -> Prop where
  | q5BaseTemplate {r : Nat}
      (h : c15Q5BaseTemplateLMod16 r)
      (boundary :
        ∀ u, C15AcceptedBaseTemplateBoundary (c15AcceptedBaseTemplateQ u)) :
      C15ResidualLaunchRowOutcome C15AuditedPullback.q5 r
  | q5L5
      (inputClass :
        ∀ q, Nat.ModEq (2 ^ 22) q (c15Q5InputResidue 5) ->
          C15Q5L5InputClassDirectDescent27 q)
      (lands :
        ∀ a, C15DirectDescentMenuTarget (1572864 * a + 1210395)) :
      C15ResidualLaunchRowOutcome C15AuditedPullback.q5 5
  | q5L15
      (inputClass :
        ∀ q, Nat.ModEq (2 ^ 22) q (c15Q5InputResidue 15) ->
          C15Q5L15InputClassDirectChasePrefix q)
      (lands :
        ∀ a, C15DirectDescentMenuTarget (995328 * a + 287071)) :
      C15ResidualLaunchRowOutcome C15AuditedPullback.q5 15
  | q3BaseTemplate {r : Nat}
      (h : c15Q3BaseTemplateLMod16 r)
      (boundary :
        ∀ u, C15AcceptedBaseTemplateBoundary (c15AcceptedBaseTemplateQ u)) :
      C15ResidualLaunchRowOutcome C15AuditedPullback.q3 r
  | q3L6
      (inputClass :
        ∀ q, Nat.ModEq (2 ^ 28) q (c15Q3InputResidue 6) ->
          C15Q3L6InputClassDirectDescent43 q)
      (lands :
        ∀ a, C15DirectDescentMenuTarget (3981312 * a + 3500715)) :
      C15ResidualLaunchRowOutcome C15AuditedPullback.q3 6
  | q3L14
      (inputClass :
        ∀ q, Nat.ModEq (2 ^ 28) q (c15Q3InputResidue 14) ->
          C15Q3L14InputClassDirectChasePrefix q)
      (hybrid : C15Q3L14HybridDirectDescentTailCompression) :
      C15ResidualLaunchRowOutcome C15AuditedPullback.q3 14
def c15_q5_residual_launch_row_outcome
    (r : Nat) (h : c15Q5ResidualLMod16 r) :
    C15ResidualLaunchRowOutcome C15AuditedPullback.q5 r := by
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact C15ResidualLaunchRowOutcome.q5BaseTemplate
      (Or.inl rfl) c15_accepted_base_template_boundary
  · exact C15ResidualLaunchRowOutcome.q5L5
      c15_q5_L5_input_class_direct_descent27
      c15_q5_L5_terminal_menu_target
  · exact C15ResidualLaunchRowOutcome.q5BaseTemplate
      (Or.inr (Or.inl rfl)) c15_accepted_base_template_boundary
  · exact C15ResidualLaunchRowOutcome.q5BaseTemplate
      (Or.inr (Or.inr rfl)) c15_accepted_base_template_boundary
  · exact C15ResidualLaunchRowOutcome.q5L15
      c15_q5_L15_input_class_direct_chase_prefix
      c15_q5_L15_terminal_menu_target
def c15_q3_residual_launch_row_outcome
    (r : Nat) (h : c15Q3ResidualLMod16 r) :
    C15ResidualLaunchRowOutcome C15AuditedPullback.q3 r := by
  rcases h with rfl | rfl | rfl
  · exact C15ResidualLaunchRowOutcome.q3BaseTemplate
      rfl c15_accepted_base_template_boundary
  · exact C15ResidualLaunchRowOutcome.q3L6
      c15_q3_L6_input_class_direct_descent43
      c15_q3_L6_terminal_menu_target
  · exact C15ResidualLaunchRowOutcome.q3L14
      c15_q3_L14_input_class_direct_chase_prefix
      c15_q3_L14_hybrid_direct_descent_tail_compression
structure C15FiniteResidueFamilySpliceReduction (L : Nat) where
  cylinders : C15AuditedInputCylinders L
  q5_suffix_continuation :
    ∀ q, Nat.ModEq (2 ^ 22) q (c15Q5InputResidue L) ->
      C15Q5InputClassAuditedSuffixContinuation L q
  q3_suffix_continuation :
    ∀ q, Nat.ModEq (2 ^ 28) q (c15Q3InputResidue L) ->
      C15Q3InputClassAuditedSuffixContinuation L q
noncomputable def c15_finite_residue_family_splice_reduction (L : Nat) (_hL : 1 <= L) :
    C15FiniteResidueFamilySpliceReduction L :=
  { cylinders := c15_audited_input_cylinders L
    q5_suffix_continuation := c15_q5_input_class_audited_suffix_continuation L
    q3_suffix_continuation := c15_q3_input_class_audited_suffix_continuation L }
structure C15ExhaustiveFiniteResidualMenu where
  landing : C15ResidualRepresentativeLandingPackage
  hybrid : C15Q3L14HybridDirectDescentTailCompression
  splice_reduction :
    ∀ L, 1 <= L -> C15FiniteResidueFamilySpliceReduction L
  q5_ledger_covers :
    ∀ r, c15Q5ResidualLMod16 r ->
      c15Q5BaseTemplateLMod16 r ∨ c15Q5DirectChaseLMod16 r
  q3_ledger_covers :
    ∀ r, c15Q3ResidualLMod16 r ->
      c15Q3BaseTemplateLMod16 r ∨ c15Q3DirectChaseLMod16 r
  q5_base_template_boundary :
    ∀ r u, c15Q5BaseTemplateLMod16 r ->
      c15Q5ResidualLMod16 r ∧
        C15AcceptedBaseTemplateBoundary (c15AcceptedBaseTemplateQ u)
  q3_base_template_boundary :
    ∀ r u, c15Q3BaseTemplateLMod16 r ->
      c15Q3ResidualLMod16 r ∧
        C15AcceptedBaseTemplateBoundary (c15AcceptedBaseTemplateQ u)
  q5_row_outcome :
    ∀ r, c15Q5ResidualLMod16 r ->
      C15ResidualLaunchRowOutcome C15AuditedPullback.q5 r
  q3_row_outcome :
    ∀ r, c15Q3ResidualLMod16 r ->
      C15ResidualLaunchRowOutcome C15AuditedPullback.q3 r
  dyadic_no_silent_gap :
    ∀ M r, 0 < M -> r < M -> C15DyadicResidueSplit M r
noncomputable def c15_exhaustive_finite_residual_menu : C15ExhaustiveFiniteResidualMenu where
  landing := c15_residual_representative_landing_package
  hybrid := c15_q3_L14_hybrid_direct_descent_tail_compression
  splice_reduction := c15_finite_residue_family_splice_reduction
  q5_ledger_covers := c15_q5_ledger_row_covers_residual_class
  q3_ledger_covers := c15_q3_ledger_row_covers_residual_class
  q5_base_template_boundary := c15_q5_base_template_row_boundary
  q3_base_template_boundary := c15_q3_base_template_row_boundary
  q5_row_outcome := c15_q5_residual_launch_row_outcome
  q3_row_outcome := c15_q3_residual_launch_row_outcome
  dyadic_no_silent_gap := c15_dyadic_residue_split
structure C15AuditedResidualMenuLandsInDirectDescent where
  exhaustive : C15ExhaustiveFiniteResidualMenu
  directMenu : C15DirectDescentResidueMenu
  directMenu_eq : directMenu = exhaustive.landing.directMenu
  q5_L5_lands :
    ∀ a, C15DirectDescentMenuTarget (1572864 * a + 1210395)
  q5_L15_lands :
    ∀ a, C15DirectDescentMenuTarget (995328 * a + 287071)
  q3_L6_lands :
    ∀ a, C15DirectDescentMenuTarget (3981312 * a + 3500715)
  q3_L14_tail_11 :
    ∀ a, a % 32 = 5 -> C15DirectDescentMenuTarget (9565938 * a + 3125777)
  q3_L14_tail_43 :
    ∀ a, a % 32 = 21 -> C15DirectDescentMenuTarget (9565938 * a + 3125777)
  q3_L14_tail_27 :
    ∀ a, a % 128 = 109 -> C15DirectDescentMenuTarget (9565938 * a + 3125777)
  q3_L14_subleaf955 :
    ∀ a, a % 1024 = 955 ->
      ∃ d, a = 1024 * d + 955 ∧
        C15DirectDescentMenuTarget (4132485216 * d + 3855345427)
  q3_L14_subleaf699 :
    ∀ a, a % 2048 = 699 ->
      ∃ d, a = 2048 * d + 699 ∧
        C15DirectDescentMenuTarget (8264970432 * d + 2822224123)
  q3_L14_subleaf1467 :
    ∀ a, a % 2048 = 1467 ->
      ∃ d, a = 2048 * d + 1467 ∧
        C15DirectDescentMenuTarget (8264970432 * d + 5921588035)
noncomputable def c15_audited_residual_menu_lands_in_direct_descent :
    C15AuditedResidualMenuLandsInDirectDescent where
  exhaustive := c15_exhaustive_finite_residual_menu
  directMenu := c15_direct_descent_residue_menu
  directMenu_eq := rfl
  q5_L5_lands := c15_q5_L5_terminal_menu_target
  q5_L15_lands := c15_q5_L15_terminal_menu_target
  q3_L6_lands := c15_q3_L6_terminal_menu_target
  q3_L14_tail_11 := c15_q3_L14_tail_menu_target11_of_mod32_eq5
  q3_L14_tail_43 := c15_q3_L14_tail_menu_target43_of_mod32_eq21
  q3_L14_tail_27 := c15_q3_L14_tail_menu_target27_of_mod128_eq109
  q3_L14_subleaf955 := c15_q3_L14_subleaf955_menu_target_of_mod1024
  q3_L14_subleaf699 := c15_q3_L14_subleaf699_menu_target_of_mod2048
  q3_L14_subleaf1467 := c15_q3_L14_subleaf1467_menu_target_of_mod2048
structure C15AuditBoundaryForResidualMenu where
  exhaustive : C15ExhaustiveFiniteResidualMenu
  lands_in_direct_descent : C15AuditedResidualMenuLandsInDirectDescent
  L15_closes_through_31 :
    ∀ a, C15DirectDescentMenuTarget (995328 * a + 287071)
  imported_bounded_stock :
    C17FixedStockBoundedKernelEvidence
  imported_terminal_stock_closed :
    C17RecordedTerminalDownstreamStockLedgerClosed
noncomputable def c15_audit_boundary_for_residual_menu : C15AuditBoundaryForResidualMenu where
  exhaustive := c15_exhaustive_finite_residual_menu
  lands_in_direct_descent := c15_audited_residual_menu_lands_in_direct_descent
  L15_closes_through_31 := c15_q5_L15_terminal_menu_target
  imported_bounded_stock := c17_fixed_stock_bounded_kernel_evidence
  imported_terminal_stock_closed := c17_lemma1a_recorded_terminal_downstream_stock_closed
def c15Class21OddResidueClass (L : Nat) : C11OneOddResidueClass where
  exponent := 6
  residue := c15Class21Residue L
  residue_odd := c15_class21_residue_odd L
structure C15Class21TerminalSupport (L : Nat) where
  terminal : C11TerminalClass21
  terminal_eq : terminal.C21 = c15Class21OddResidueClass L
  defining_residue :
    (3 ^ L * terminal.C21.residue) % 64 = 37
  valuation_two :
    ∀ u, c3V2 (3 ^ L * (terminal.C21.residue + 64 * u) - 1) = 2
  next_length_one :
    ∀ u, c3V2 (c15Class21CNext L u + 1) = 1
  next_residue_9_mod16 :
    ∀ u, c15Class21CNext L u % 16 = 9
def c15_class21_terminal_support (L : Nat) : C15Class21TerminalSupport L := by
  let terminal : C11TerminalClass21 :=
    { C21 := c15Class21OddResidueClass L
      C21_exponent := rfl
      valuation_two := ∀ u, c3V2 (3 ^ L * (c15Class21Residue L + 64 * u) - 1) = 2
      next_length_one := ∀ u, c3V2 (c15Class21CNext L u + 1) = 1
      next_residue_9_mod16 := ∀ u, c15Class21CNext L u % 16 = 9
      negative_gap := ∀ u, c15Class21CNext L u % 16 = 9 }
  refine
    { terminal := terminal
      terminal_eq := rfl
      defining_residue := ?_
      valuation_two := ?_
      next_length_one := ?_
      next_residue_9_mod16 := ?_ }
  · exact c15_class21_residue_defining_mod64 L
  · intro u
    exact c15_class21_raw_v2_eq_two L u
  · intro u
    exact c15_class21_next_length_one L u
  · intro u
    exact c15_class21_cnext_mod16 L u
def c15_c11_terminal_class21 (L : Nat) : C11TerminalClass21 :=
  (c15_class21_terminal_support L).terminal
def c15_class21_to_c11_pullback
    (L : Nat) (Y : C11TerminalFreeExactPathFamily) :
    C11Class21Pullback Y :=
  c11_terminal_free_exact_path_class21_pullback Y (c15_c11_terminal_class21 L)
    (by
      change ∀ u, c3V2 (3 ^ L * (c15Class21Residue L + 64 * u) - 1) = 2
      intro u
      exact c15_class21_raw_v2_eq_two L u)
    (by
      change ∀ u, c3V2 (c15Class21CNext L u + 1) = 1
      intro u
      exact c15_class21_next_length_one L u)
    (by
      change ∀ u, c15Class21CNext L u % 16 = 9
      intro u
      exact c15_class21_cnext_mod16 L u)
    (by
      change ∀ u, c15Class21CNext L u % 16 = 9
      intro u
      exact c15_class21_cnext_mod16 L u)

structure C17KState where
  centeredC : Nat
  tParity : Bool
  pairLabel : Nat
  centeredC_lt : centeredC < 3 ^ 17
  deriving Repr
def C17KState.toC5KState (state : C17KState) : C5KState :=
  { centeredC := state.centeredC
    tParity := state.tParity
    pairLabel := state.pairLabel }
theorem c17_kstate_centered_bound (state : C17KState) :
    state.centeredC < 3 ^ 17 :=
  state.centeredC_lt
structure C17ActiveLiveBranch where
  sourceOdd : Nat
  sourceOdd_odd : sourceOdd % 2 = 1
  liveAt : Nat -> Prop
  projectedK : Nat -> C17KState
def C17BranchProjectsToKAt
    (branch : C17ActiveLiveBranch) (step : Nat) (state : C17KState) : Prop :=
  branch.liveAt step ∧ branch.projectedK step = state
def C17ReachableKState (state : C17KState) : Prop :=
  ∃ branch : C17ActiveLiveBranch,
  ∃ step : Nat,
    C17BranchProjectsToKAt branch step state
theorem c17_reachable_kstate_centered_bound
    {state : C17KState} (_hreachable : C17ReachableKState state) :
    state.centeredC < 3 ^ 17 :=
  state.centeredC_lt
theorem c17_reachable_kstate_to_c5_coordinates
    {state : C17KState} (_hreachable : C17ReachableKState state) :
    (state.toC5KState).centeredC = state.centeredC ∧
      (state.toC5KState).tParity = state.tParity ∧
      (state.toC5KState).pairLabel = state.pairLabel := by
  exact ⟨rfl, rfl, rfl⟩
def c17CenteredD : Nat := 129140163
theorem c17CenteredD_eq_three_pow_17 : c17CenteredD = 3 ^ 17 := by
  native_decide
def c17CenteredA : Nat := 86093442
theorem c17CenteredA_eq_two_mul_three_pow_16 : c17CenteredA = 2 * 3 ^ 16 := by
  native_decide
def c17InitialCentered (q : Nat) : Nat :=
  (3 * (q % c17CenteredA) - 1) / 2
theorem c17_initial_centered_bound (q : Nat) :
    c17InitialCentered q < 3 ^ 17 := by
  unfold c17InitialCentered c17CenteredA
  omega
theorem c17_initial_centered_mod3 (q : Nat) (hodd : q % 2 = 1) :
    c17InitialCentered q % 3 = 1 := by
  unfold c17InitialCentered c17CenteredA
  omega
def c17SurvivorResidue (c8 : Nat) : Nat :=
  match c8 % 8 with
  | 0 => 0 | 1 => 5 | 2 => 2 | 3 => 7
  | 4 => 4 | 5 => 1 | 6 => 6 | _ => 3
theorem c17SurvivorResidue_bound (c : Nat) :
    c17SurvivorResidue c < 8 := by
  unfold c17SurvivorResidue
  split <;> omega
theorem c17SurvivorResidue_spec (centeredC : Nat) :
    (centeredC + c17CenteredD * c17SurvivorResidue (centeredC % 8)) % 8 = 0 := by
  have hcases :
      centeredC % 8 = 0 ∨ centeredC % 8 = 1 ∨ centeredC % 8 = 2 ∨
      centeredC % 8 = 3 ∨ centeredC % 8 = 4 ∨ centeredC % 8 = 5 ∨
      centeredC % 8 = 6 ∨ centeredC % 8 = 7 := by
    omega
  rcases hcases with h | h | h | h | h | h | h | h <;>
    simp [c17SurvivorResidue, c17CenteredD, h] <;> omega
def c17CenteredNext (centeredC : Nat) : Nat :=
  (centeredC + c17CenteredD * c17SurvivorResidue (centeredC % 8)) / 8
theorem c17_centered_numer_eq_eight_mul_next (centeredC : Nat) :
    centeredC + c17CenteredD * c17SurvivorResidue (centeredC % 8) =
      8 * c17CenteredNext centeredC := by
  unfold c17CenteredNext
  have hs := c17SurvivorResidue_spec centeredC
  have h := Nat.div_add_mod
    (centeredC + c17CenteredD * c17SurvivorResidue (centeredC % 8)) 8
  rw [hs] at h
  omega
theorem c17CenteredNext_bound
    (centeredC : Nat) (hC : centeredC < c17CenteredD) :
    c17CenteredNext centeredC < c17CenteredD := by
  unfold c17CenteredD at hC ⊢
  unfold c17CenteredNext
  unfold c17CenteredD
  have hm := c17SurvivorResidue_bound (centeredC % 8)
  omega
inductive C17CoarsePair where
  | p04
  | p15
  | p26
  | p37
  deriving DecidableEq, Repr
def C17CoarsePair.label : C17CoarsePair -> Nat
  | .p04 => 0
  | .p15 => 1
  | .p26 => 2
  | .p37 => 3
def c17PairFromCoarse (cmod24 : Nat) (tParity : Bool) : Option C17CoarsePair :=
  match cmod24, tParity with
  | 1, true => some C17CoarsePair.p15
  | 5, false => some C17CoarsePair.p15
  | 13, true => some C17CoarsePair.p15
  | 17, false => some C17CoarsePair.p15
  | 2, false => some C17CoarsePair.p26
  | 10, true => some C17CoarsePair.p26
  | 14, false => some C17CoarsePair.p26
  | 22, true => some C17CoarsePair.p26
  | 4, true => some C17CoarsePair.p04
  | 8, false => some C17CoarsePair.p04
  | 16, true => some C17CoarsePair.p04
  | 20, false => some C17CoarsePair.p04
  | 7, true => some C17CoarsePair.p37
  | 11, false => some C17CoarsePair.p37
  | 19, true => some C17CoarsePair.p37
  | 23, false => some C17CoarsePair.p37
  | _, _ => none
theorem c17_pair_from_coarse_admits_mod3_true
    (centeredC : Nat) (hmod3 : centeredC % 3 = 1) :
    ∃ pair : C17CoarsePair,
      c17PairFromCoarse (centeredC % 24) true = some pair := by
  have h24 : centeredC % 24 < 24 := Nat.mod_lt centeredC (by omega)
  have h3_24 : centeredC % 24 % 3 = 1 := by omega
  have hcases :
      centeredC % 24 = 1 ∨ centeredC % 24 = 4 ∨
      centeredC % 24 = 7 ∨ centeredC % 24 = 10 ∨
      centeredC % 24 = 13 ∨ centeredC % 24 = 16 ∨
      centeredC % 24 = 19 ∨ centeredC % 24 = 22 := by
    omega
  rcases hcases with h | h | h | h | h | h | h | h <;>
    rw [h] <;> simp [c17PairFromCoarse]
def c17InitialKState? (q : Nat) : Option C17KState :=
  let centeredC := c17InitialCentered q
  let hcentered : centeredC < 3 ^ 17 := c17_initial_centered_bound q
  match c17PairFromCoarse (centeredC % 24) true with
  | some pair =>
      some
        { centeredC := centeredC
          tParity := true
          pairLabel := pair.label
          centeredC_lt := hcentered }
  | none => none
theorem c17_initial_kstate_total (q : Nat) (hodd : q % 2 = 1) :
    ∃ state : C17KState, c17InitialKState? q = some state := by
  have hmod3 := c17_initial_centered_mod3 q hodd
  obtain ⟨pair, hpair⟩ :=
    c17_pair_from_coarse_admits_mod3_true (c17InitialCentered q) hmod3
  exact ⟨{ centeredC := c17InitialCentered q
           tParity := true
           pairLabel := pair.label
           centeredC_lt := c17_initial_centered_bound q },
    by simp [c17InitialKState?, hpair]⟩
theorem c17_initial_kstate_total_of_odd (q : Nat) (hodd : Odd q) :
    ∃ state : C17KState, c17InitialKState? q = some state := by
  exact c17_initial_kstate_total q (Nat.odd_iff.mp hodd)
def C17KStateValidPair (state : C17KState) : Prop :=
  ∃ pair : C17CoarsePair,
    c17PairFromCoarse (state.centeredC % 24) state.tParity = some pair ∧
      state.pairLabel = pair.label
def C17KNext? (state : C17KState) : Option C17KState :=
  let nextC := c17CenteredNext state.centeredC
  let nextParity := !state.tParity
  let hNextC : nextC < 3 ^ 17 := by
    have hD : state.centeredC < c17CenteredD := by
      rw [c17CenteredD_eq_three_pow_17]
      exact state.centeredC_lt
    have h := c17CenteredNext_bound state.centeredC hD
    rw [c17CenteredD_eq_three_pow_17] at h
    exact h
  match c17PairFromCoarse (nextC % 24) nextParity with
  | some pair =>
      some
        { centeredC := nextC
          tParity := nextParity
          pairLabel := pair.label
          centeredC_lt := hNextC }
  | none => none
theorem c17_knext_deterministic
    (state₁ state₂ : C17KState) (hstate : state₁ = state₂) :
    C17KNext? state₁ = C17KNext? state₂ := by
  cases hstate
  rfl
theorem c17_knext_centered_bound
    {state state' : C17KState} (_hnext : C17KNext? state = some state') :
    state'.centeredC < 3 ^ 17 :=
  state'.centeredC_lt
theorem c17_knext_valid_pair
    {state state' : C17KState} (hnext : C17KNext? state = some state') :
    C17KStateValidPair state' := by
  cases hpair :
      c17PairFromCoarse ((c17CenteredNext state.centeredC) % 24) (!state.tParity) with
  | none =>
      simp [C17KNext?, hpair] at hnext
  | some pair =>
      simp [C17KNext?, hpair] at hnext
      cases hnext
      exact ⟨pair, hpair, rfl⟩
theorem c17_initial_kstate_valid_pair
    {q : Nat} {seed : C17KState}
    (hseed : c17InitialKState? q = some seed) :
    C17KStateValidPair seed := by
  unfold c17InitialKState? at hseed
  cases hpair :
      c17PairFromCoarse (c17InitialCentered q % 24) true with
  | none =>
      simp [hpair] at hseed
  | some pair =>
      simp [hpair] at hseed
      cases hseed
      exact ⟨pair, hpair, rfl⟩
theorem c17_knext_coordinates
    {state state' : C17KState} (hnext : C17KNext? state = some state') :
    state'.centeredC = c17CenteredNext state.centeredC ∧
      state'.tParity = !state.tParity := by
  cases hpair :
      c17PairFromCoarse ((c17CenteredNext state.centeredC) % 24) (!state.tParity) with
  | none =>
      simp [C17KNext?, hpair] at hnext
  | some _pair =>
      simp [C17KNext?, hpair] at hnext
      cases hnext
      exact ⟨rfl, rfl⟩
def c17KBreakState (state : C17KState) : Nat :=
  if state.tParity then (2 * state.centeredC + 1) / 3
  else (state.centeredC + 1) / 3
inductive C17L1Class where
  | type11
  | type21
  | exit5
  | exit13
  | exit15
  | dangerous3
  | exit19
  | smallExit3
  | intrinsic11
  deriving DecidableEq, Repr
def c17L1Class (q : Nat) : C17L1Class :=
  match q % 16 with
  | 1  => .type11
  | 9  => .type11
  | 7  => .type21
  | 5  => .exit5
  | 13 => .exit13
  | 15 => .exit15
  | 11 => .intrinsic11
  | 3  =>
      if q = 3 ∨ q = 35 then .smallExit3
      else if q % 32 = 3 then .dangerous3
      else .exit19
  | _  => .type11
def c17L1ClassIsExit : C17L1Class -> Bool
  | .exit5 | .exit13 | .exit15 | .exit19 | .smallExit3 => true
  | _ => false
def c17TwoStepOddCentered (centeredC : Nat) : Nat :=
  c17CenteredNext (c17CenteredNext centeredC)
theorem c17_two_step_odd_centered_mul_mod
    (centeredC : Nat) :
    (64 * c17TwoStepOddCentered centeredC) % c17CenteredD =
      centeredC % c17CenteredD := by
  have h0 := c17_centered_numer_eq_eight_mul_next centeredC
  have h1 := c17_centered_numer_eq_eight_mul_next
    (c17CenteredNext centeredC)
  unfold c17TwoStepOddCentered
  have h64 :
      64 * c17CenteredNext (c17CenteredNext centeredC) =
        centeredC + c17CenteredD *
          (c17SurvivorResidue (centeredC % 8) +
            8 * c17SurvivorResidue ((c17CenteredNext centeredC) % 8)) := by
    calc
      64 * c17CenteredNext (c17CenteredNext centeredC)
          = 8 * (8 * c17CenteredNext (c17CenteredNext centeredC)) := by
              omega
      _ = 8 * (c17CenteredNext centeredC +
            c17CenteredD *
              c17SurvivorResidue ((c17CenteredNext centeredC) % 8)) := by
              rw [← h1]
      _ = 8 * c17CenteredNext centeredC +
            c17CenteredD *
              (8 * c17SurvivorResidue ((c17CenteredNext centeredC) % 8)) := by
              ring
      _ = centeredC + c17CenteredD * c17SurvivorResidue (centeredC % 8) +
            c17CenteredD *
              (8 * c17SurvivorResidue ((c17CenteredNext centeredC) % 8)) := by
              rw [← h0]
      _ = centeredC + c17CenteredD *
          (c17SurvivorResidue (centeredC % 8) +
            8 * c17SurvivorResidue ((c17CenteredNext centeredC) % 8)) := by
              ring
  rw [h64]
  rw [Nat.add_mod, Nat.mul_mod]
  simp
theorem c17_two_step_odd_centered_zmod
    (centeredC : Nat) :
    (64 : ZMod (3 ^ 17)) *
      (c17TwoStepOddCentered centeredC : ZMod (3 ^ 17)) =
        (centeredC : ZMod (3 ^ 17)) := by
  calc
    (64 : ZMod (3 ^ 17)) *
        (c17TwoStepOddCentered centeredC : ZMod (3 ^ 17))
        = ((64 * c17TwoStepOddCentered centeredC : Nat) :
            ZMod (3 ^ 17)) := by
            exact (Nat.cast_mul 64
              (c17TwoStepOddCentered centeredC)).symm
    _ = (centeredC : ZMod (3 ^ 17)) := by
            exact
              (ZMod.natCast_eq_natCast_iff
                (64 * c17TwoStepOddCentered centeredC)
                centeredC (3 ^ 17)).2 (by
                  simpa [c17CenteredD_eq_three_pow_17] using
                    c17_two_step_odd_centered_mul_mod centeredC)
theorem c17_two_step_odd_centered_iter_zmod
    (centeredC steps : Nat) :
    ((64 : ZMod (3 ^ 17)) ^ steps) *
      (((c17TwoStepOddCentered^[steps]) centeredC) : ZMod (3 ^ 17)) =
        (centeredC : ZMod (3 ^ 17)) := by
  induction steps generalizing centeredC with
  | zero =>
      simp
  | succ steps ih =>
      rw [Function.iterate_succ_apply]
      have hstep := c17_two_step_odd_centered_zmod centeredC
      have htail := ih (c17TwoStepOddCentered centeredC)
      rw [pow_succ]
      calc
        (64 : ZMod (3 ^ 17)) ^ steps * 64 *
            (((c17TwoStepOddCentered^[steps])
              (c17TwoStepOddCentered centeredC)) : ZMod (3 ^ 17))
            = (64 : ZMod (3 ^ 17)) ^ steps *
                (64 *
                  (((c17TwoStepOddCentered^[steps])
                    (c17TwoStepOddCentered centeredC)) :
                      ZMod (3 ^ 17))) := by ring
        _ = 64 *
              ((64 : ZMod (3 ^ 17)) ^ steps *
                (((c17TwoStepOddCentered^[steps])
                  (c17TwoStepOddCentered centeredC)) :
                    ZMod (3 ^ 17))) := by ring
        _ = 64 *
              ((c17TwoStepOddCentered centeredC) : ZMod (3 ^ 17)) := by
              rw [htail]
        _ = (centeredC : ZMod (3 ^ 17)) := by
              exact hstep
theorem c17_two_step_odd_centered_bound
    {centeredC : Nat} (hC : centeredC < 3 ^ 17) :
    c17TwoStepOddCentered centeredC < 3 ^ 17 := by
  unfold c17TwoStepOddCentered
  have hD : centeredC < c17CenteredD := by
    simpa [c17CenteredD_eq_three_pow_17] using hC
  have h1 := c17CenteredNext_bound centeredC hD
  have h2 := c17CenteredNext_bound (c17CenteredNext centeredC) h1
  simpa [c17CenteredD_eq_three_pow_17] using h2
theorem c17_two_step_odd_centered_iter_bound
    {centeredC steps : Nat} (hC : centeredC < 3 ^ 17) :
    (c17TwoStepOddCentered^[steps]) centeredC < 3 ^ 17 := by
  induction steps generalizing centeredC with
  | zero =>
      simpa using hC
  | succ steps ih =>
      rw [Function.iterate_succ_apply]
      exact ih (c17_two_step_odd_centered_bound hC)
def c17OddCenteredExitsDetectorBool (centeredC : Nat) : Bool :=
  if hcentered : centeredC < 3 ^ 17 then
    match c17PairFromCoarse (centeredC % 24) true with
    | none => true
    | some pair =>
        let state : C17KState :=
          { centeredC := centeredC
            tParity := true
            pairLabel := pair.label
            centeredC_lt := hcentered }
        c17L1ClassIsExit (c17L1Class (c17KBreakState state)) ||
          (C17KNext? state).isNone
  else true
def c17EvenSuccessorExitsDetectorBool (centeredC : Nat) : Bool :=
  let nextC := c17CenteredNext centeredC
  if hnext : nextC < 3 ^ 17 then
    match c17PairFromCoarse (nextC % 24) false with
    | none => true
    | some pair =>
        let state : C17KState :=
          { centeredC := nextC
            tParity := false
            pairLabel := pair.label
            centeredC_lt := hnext }
        c17L1ClassIsExit (c17L1Class (c17KBreakState state)) ||
          (C17KNext? state).isNone
  else true
def c17OddCenteredCycleHasDetectorExit : Nat -> Nat -> Nat -> Bool
  | 0, _start, _centeredC => false
  | fuel + 1, start, centeredC =>
      if c17OddCenteredExitsDetectorBool centeredC ||
          c17EvenSuccessorExitsDetectorBool centeredC then
        true
      else
        let nextC := c17TwoStepOddCentered centeredC
        if nextC == start then false
        else c17OddCenteredCycleHasDetectorExit fuel start nextC
def c17ActiveKTwoStepCycleExitCoverageBool : Bool :=
  c17OddCenteredCycleHasDetectorExit (3 ^ 15 + 1) 1 1 &&
    c17OddCenteredCycleHasDetectorExit (3 ^ 15 + 1) 4 4 &&
      c17OddCenteredCycleHasDetectorExit (3 ^ 15 + 1) 7 7
theorem c17_active_k_two_step_cycle_exit_coverage :
    c17ActiveKTwoStepCycleExitCoverageBool = true := by
  native_decide
theorem c17_odd_centered_cycle_scan_one_true :
    c17OddCenteredCycleHasDetectorExit (3 ^ 15 + 1) 1 1 = true := by
  have h := c17_active_k_two_step_cycle_exit_coverage
  simp [c17ActiveKTwoStepCycleExitCoverageBool] at h
  norm_num
  exact h.1.1
theorem c17_odd_centered_cycle_scan_four_true :
    c17OddCenteredCycleHasDetectorExit (3 ^ 15 + 1) 4 4 = true := by
  have h := c17_active_k_two_step_cycle_exit_coverage
  simp [c17ActiveKTwoStepCycleExitCoverageBool] at h
  norm_num
  exact h.1.2
theorem c17_odd_centered_cycle_scan_seven_true :
    c17OddCenteredCycleHasDetectorExit (3 ^ 15 + 1) 7 7 = true := by
  have h := c17_active_k_two_step_cycle_exit_coverage
  simp [c17ActiveKTwoStepCycleExitCoverageBool] at h
  norm_num
  exact h.2
theorem c17_orderOf_64_zmod_three_pow_17 :
    orderOf (64 : ZMod (3 ^ 17)) = 3 ^ 15 := by
  have hp : Nat.Prime 3 := by norm_num
  have hm0 : Not ((2 : Nat) = 0) := by norm_num
  have hpm : 2 + 2 <= 3 * 2 := by norm_num
  have ha : Not (Dvd.dvd (3 : Int) (7 : Int)) := by norm_num
  have h := ZMod.orderOf_one_add_mul_prime_pow hp 2 hm0 hpm 7 ha 15
  norm_num at h
  exact h
def c17ZModUnit64 : (ZMod (3 ^ 17))ˣ :=
  ZMod.unitOfCoprime 64 (by norm_num : Nat.Coprime 64 (3 ^ 17))
theorem c17_orderOf_unit64_zmod_three_pow_17 :
    orderOf c17ZModUnit64 = 3 ^ 15 := by
  have hunit :
      orderOf (c17ZModUnit64 : ZMod (3 ^ 17)) =
        orderOf c17ZModUnit64 := orderOf_units
  rw [← hunit]
  unfold c17ZModUnit64
  rw [ZMod.coe_unitOfCoprime]
  exact c17_orderOf_64_zmod_three_pow_17
def c17ZModReduce17To9 : ZMod (3 ^ 17) →+* ZMod 9 :=
  ZMod.castHom (show Dvd.dvd 9 (3 ^ 17) by norm_num) (ZMod 9)
def c17ZModUnitReduce17To9 : (ZMod (3 ^ 17))ˣ →* (ZMod 9)ˣ :=
  Units.map c17ZModReduce17To9.toMonoidWithZeroHom
theorem c17_unit64_reduces_to_one_mod9 :
    c17ZModUnit64 ∈ c17ZModUnitReduce17To9.ker := by
  change c17ZModUnitReduce17To9 c17ZModUnit64 = 1
  ext
  native_decide
theorem c17_unit_reduce17_to9_surjective :
    Function.Surjective c17ZModUnitReduce17To9 := by
  unfold c17ZModUnitReduce17To9 c17ZModReduce17To9
  simpa [ZMod.unitsMap_def] using
    (ZMod.unitsMap_surjective (show Dvd.dvd 9 (3 ^ 17) by norm_num))
theorem c17_unit_reduce17_to9_kernel_card :
    Nat.card c17ZModUnitReduce17To9.ker = 3 ^ 15 := by
  have hmul := Subgroup.card_mul_index c17ZModUnitReduce17To9.ker
  have hindex : c17ZModUnitReduce17To9.ker.index = Nat.card ((ZMod 9)ˣ) := by
    rw [Subgroup.index_ker]
    have hrange : c17ZModUnitReduce17To9.range = ⊤ := by
      rw [MonoidHom.range_eq_top]
      exact c17_unit_reduce17_to9_surjective
    rw [hrange, Subgroup.card_top]
  rw [hindex] at hmul
  have hdomain : Nat.card ((ZMod (3 ^ 17))ˣ) = 2 * 3 ^ 16 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    rw [show 3 ^ 17 = 3 ^ (16 + 1) by ring]
    rw [Nat.totient_prime_pow_succ (by norm_num : Nat.Prime 3) 16]
    norm_num
  have hrangeCard : Nat.card ((ZMod 9)ˣ) = 6 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    native_decide
  rw [hdomain, hrangeCard] at hmul
  omega
theorem c17_unit64_zpowers_eq_reduce17_to9_kernel :
    Subgroup.zpowers c17ZModUnit64 = c17ZModUnitReduce17To9.ker := by
  have hle :
      Subgroup.zpowers c17ZModUnit64 ≤ c17ZModUnitReduce17To9.ker :=
    Subgroup.zpowers_le_of_mem c17_unit64_reduces_to_one_mod9
  let H : Subgroup c17ZModUnitReduce17To9.ker :=
    (Subgroup.zpowers c17ZModUnit64).subgroupOf c17ZModUnitReduce17To9.ker
  have hHcard : Nat.card H = Nat.card c17ZModUnitReduce17To9.ker := by
    have hsub :
        Nat.card H = Nat.card (Subgroup.zpowers c17ZModUnit64) := by
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rw [hsub, Nat.card_zpowers, c17_orderOf_unit64_zmod_three_pow_17,
      c17_unit_reduce17_to9_kernel_card]
  have hHtop : H = ⊤ := Subgroup.eq_top_of_card_eq H hHcard
  apply le_antisymm hle
  intro x hx
  have hxH : (⟨x, hx⟩ : c17ZModUnitReduce17To9.ker) ∈ H := by
    rw [hHtop]
    exact Subgroup.mem_top _
  exact hxH
theorem c17_unit_ratio_same_mod9_mem_kernel
    {c r : Nat}
    (hc : Nat.Coprime c (3 ^ 17))
    (hr : Nat.Coprime r (3 ^ 17))
    (hmod : (c : ZMod 9) = (r : ZMod 9)) :
    (ZMod.unitOfCoprime c hc * (ZMod.unitOfCoprime r hr)⁻¹ :
      (ZMod (3 ^ 17))ˣ) ∈ c17ZModUnitReduce17To9.ker := by
  change c17ZModUnitReduce17To9
      (ZMod.unitOfCoprime c hc * (ZMod.unitOfCoprime r hr)⁻¹) = 1
  rw [map_mul, map_inv]
  have hunit :
      c17ZModUnitReduce17To9 (ZMod.unitOfCoprime c hc) =
        c17ZModUnitReduce17To9 (ZMod.unitOfCoprime r hr) := by
    ext
    unfold c17ZModUnitReduce17To9 c17ZModReduce17To9
    simpa [ZMod.coe_unitOfCoprime] using hmod
  rw [hunit, mul_inv_cancel]
theorem c17_unit_ratio_same_mod9_mem_unit64_zpowers
    {c r : Nat}
    (hc : Nat.Coprime c (3 ^ 17))
    (hr : Nat.Coprime r (3 ^ 17))
    (hmod : (c : ZMod 9) = (r : ZMod 9)) :
    (ZMod.unitOfCoprime c hc * (ZMod.unitOfCoprime r hr)⁻¹ :
      (ZMod (3 ^ 17))ˣ) ∈ Subgroup.zpowers c17ZModUnit64 := by
  rw [c17_unit64_zpowers_eq_reduce17_to9_kernel]
  exact c17_unit_ratio_same_mod9_mem_kernel hc hr hmod
theorem c17_unit_ratio_same_mod9_eq_unit64_pow
    {c r : Nat}
    (hc : Nat.Coprime c (3 ^ 17))
    (hr : Nat.Coprime r (3 ^ 17))
    (hmod : (c : ZMod 9) = (r : ZMod 9)) :
    ∃ n : Nat,
      c17ZModUnit64 ^ n =
        (ZMod.unitOfCoprime c hc * (ZMod.unitOfCoprime r hr)⁻¹ :
          (ZMod (3 ^ 17))ˣ) := by
  have hz := c17_unit_ratio_same_mod9_mem_unit64_zpowers hc hr hmod
  have hpowers :
      (ZMod.unitOfCoprime c hc * (ZMod.unitOfCoprime r hr)⁻¹ :
        (ZMod (3 ^ 17))ˣ) ∈ Submonoid.powers c17ZModUnit64 := by
    rw [mem_powers_iff_mem_zpowers]
    exact hz
  rw [Submonoid.mem_powers_iff] at hpowers
  exact hpowers
theorem c17_unit64_pow_mul_right_zmod
    {c r n : Nat}
    (hc : Nat.Coprime c (3 ^ 17))
    (hr : Nat.Coprime r (3 ^ 17))
    (hpow :
      c17ZModUnit64 ^ n =
        (ZMod.unitOfCoprime c hc * (ZMod.unitOfCoprime r hr)⁻¹ :
          (ZMod (3 ^ 17))ˣ)) :
    ((64 : ZMod (3 ^ 17)) ^ n) * (r : ZMod (3 ^ 17)) =
      (c : ZMod (3 ^ 17)) := by
  have hval :=
    congrArg (fun u : (ZMod (3 ^ 17))ˣ => (u : ZMod (3 ^ 17))) hpow
  have hval' :
      ((64 : ZMod (3 ^ 17)) ^ n) =
        (c : ZMod (3 ^ 17)) *
          (((ZMod.unitOfCoprime r hr)⁻¹ : (ZMod (3 ^ 17))ˣ) :
            ZMod (3 ^ 17)) := by
    simpa [c17ZModUnit64, ZMod.coe_unitOfCoprime,
      Units.val_pow_eq_pow_val] using hval
  rw [hval']
  have hcancel :
      (((ZMod.unitOfCoprime r hr)⁻¹ : (ZMod (3 ^ 17))ˣ) :
          ZMod (3 ^ 17)) *
        (r : ZMod (3 ^ 17)) = 1 := by
    have hunit :=
      congrArg (fun u : (ZMod (3 ^ 17))ˣ => (u : ZMod (3 ^ 17)))
        (inv_mul_cancel (ZMod.unitOfCoprime r hr))
    simpa only [Units.val_inv_eq_inv_val, ZMod.coe_unitOfCoprime,
      Units.val_one] using hunit
  rw [mul_assoc, hcancel, mul_one]
theorem c17_two_step_iter_eq_representative_of_unit64_pow
    {c r n : Nat}
    (hcBound : c < 3 ^ 17)
    (hrBound : r < 3 ^ 17)
    (hc : Nat.Coprime c (3 ^ 17))
    (hr : Nat.Coprime r (3 ^ 17))
    (hpow :
      c17ZModUnit64 ^ n =
        (ZMod.unitOfCoprime c hc * (ZMod.unitOfCoprime r hr)⁻¹ :
          (ZMod (3 ^ 17))ˣ)) :
    (c17TwoStepOddCentered^[n]) c = r := by
  have hiter := c17_two_step_odd_centered_iter_zmod c n
  have hr :=
    c17_unit64_pow_mul_right_zmod hc hr hpow
  have hz :
      (((c17TwoStepOddCentered^[n]) c : Nat) : ZMod (3 ^ 17)) =
        (r : ZMod (3 ^ 17)) := by
    have hunit : IsUnit ((64 : ZMod (3 ^ 17)) ^ n) :=
      IsUnit.pow n
        (ZMod.unitOfCoprime 64
          (by norm_num : Nat.Coprime 64 (3 ^ 17))).isUnit
    exact hunit.mul_right_injective (by
      calc
        ((64 : ZMod (3 ^ 17)) ^ n) *
            (((c17TwoStepOddCentered^[n]) c : Nat) : ZMod (3 ^ 17))
            = (c : ZMod (3 ^ 17)) := hiter
        _ = ((64 : ZMod (3 ^ 17)) ^ n) *
              (r : ZMod (3 ^ 17)) := hr.symm)
  have hmod :=
    (ZMod.natCast_eq_natCast_iff
      ((c17TwoStepOddCentered^[n]) c) r (3 ^ 17)).1 hz
  exact Nat.ModEq.eq_of_lt_of_lt hmod
    (c17_two_step_odd_centered_iter_bound hcBound) hrBound
theorem c17_two_step_orbit_reaches_representative_of_same_mod9
    {c r : Nat}
    (hcBound : c < 3 ^ 17)
    (hrBound : r < 3 ^ 17)
    (hc : Nat.Coprime c (3 ^ 17))
    (hr : Nat.Coprime r (3 ^ 17))
    (hmod : (c : ZMod 9) = (r : ZMod 9)) :
    ∃ n : Nat, (c17TwoStepOddCentered^[n]) c = r := by
  obtain ⟨n, hpow⟩ :=
    c17_unit_ratio_same_mod9_eq_unit64_pow hc hr hmod
  exact ⟨n,
    c17_two_step_iter_eq_representative_of_unit64_pow
      hcBound hrBound hc hr hpow⟩
theorem c17_odd_centered_mod9_cases
    {centeredC : Nat}
    (hmod3 : centeredC % 3 = 1) :
    centeredC % 9 = 1 ∨ centeredC % 9 = 4 ∨ centeredC % 9 = 7 := by
  have h9 : centeredC % 9 < 9 := Nat.mod_lt centeredC (by norm_num)
  have h3 : centeredC % 9 % 3 = 1 := by
    rw [Nat.mod_mod_of_dvd centeredC (by norm_num : 3 ∣ 9)]
    exact hmod3
  omega
def C17BranchFollowsKStep (branch : C17ActiveLiveBranch) : Prop :=
  ∀ step state nextState,
    C17BranchProjectsToKAt branch step state ->
      C17KNext? state = some nextState ->
        C17BranchProjectsToKAt branch (step + 1) nextState
def C17KIter? : C17KState -> Nat -> Option C17KState
  | state, 0 => some state
  | state, step + 1 => (C17KNext? state).bind (fun state' => C17KIter? state' step)
theorem c17_kiter_zero (state : C17KState) :
    C17KIter? state 0 = some state := rfl
theorem c17_kiter_succ_none
    (state : C17KState) (step : Nat) (hnext : C17KNext? state = none) :
    C17KIter? state (step + 1) = none := by
  simp [C17KIter?, hnext]
theorem c17_kiter_succ_some
    (state state' : C17KState) (step : Nat)
    (hnext : C17KNext? state = some state') :
    C17KIter? state (step + 1) = C17KIter? state' step := by
  simp [C17KIter?, hnext]
theorem c17_kiter_valid_pair_of_initial
    {seed state : C17KState} {step : Nat}
    (hvalid : C17KStateValidPair seed)
    (hiter : C17KIter? seed step = some state) :
    C17KStateValidPair state := by
  induction step generalizing seed with
  | zero =>
      simp [C17KIter?] at hiter
      cases hiter
      exact hvalid
  | succ step ih =>
      cases hnext : C17KNext? seed with
      | none =>
          simp [C17KIter?, hnext] at hiter
      | some midState =>
          have htail : C17KIter? midState step = some state := by
            simpa [C17KIter?, hnext] using hiter
          exact ih (c17_knext_valid_pair hnext) htail
theorem c17_step_mod_two_flip (step : Nat) :
    (step + 1) % 2 = if step % 2 = 0 then 1 else 0 := by
  by_cases h : step % 2 = 0
  · rw [if_pos h]
    omega
  · rw [if_neg h]
    have hstep : step % 2 = 1 := by omega
    omega
def c17CenteredNextIter : Nat -> Nat -> Nat
  | 0, centeredC => centeredC
  | step + 1, centeredC => c17CenteredNextIter step (c17CenteredNext centeredC)
theorem c17_korbit_tracks_break_coordinates
    (seed : C17KState) (step : Nat) (stateAtStep : C17KState)
    (hiter : C17KIter? seed step = some stateAtStep) :
    stateAtStep.centeredC = c17CenteredNextIter step seed.centeredC ∧
      stateAtStep.tParity = (if step % 2 = 0 then seed.tParity else !seed.tParity) := by
  induction step generalizing seed stateAtStep with
  | zero =>
      simp [C17KIter?] at hiter
      cases hiter
      simp [c17CenteredNextIter]
  | succ step ih =>
      cases hnext : C17KNext? seed with
      | none =>
          simp [C17KIter?, hnext] at hiter
      | some nextState =>
          have htail : C17KIter? nextState step = some stateAtStep := by
            simpa [C17KIter?, hnext] using hiter
          obtain ⟨hCtail, hPtail⟩ := ih nextState stateAtStep htail
          obtain ⟨hCnext, hPnext⟩ := c17_knext_coordinates hnext
          refine ⟨?_, ?_⟩
          · simp [c17CenteredNextIter, hCtail, hCnext]
          · rw [hPtail, hPnext]
            have hflip := c17_step_mod_two_flip step
            cases hseedParity : seed.tParity <;>
              by_cases hstepZero : step % 2 = 0 <;>
                simp [hstepZero] at hflip ⊢ <;> rw [hflip]
def C17ReachableKStateFollowing (state : C17KState) : Prop :=
  ∃ q : Nat,
  ∃ _ : q % 2 = 1,
  ∃ seed : C17KState,
  ∃ step : Nat,
    c17InitialKState? q = some seed ∧
      C17KIter? seed step = some state
theorem c17_kiter_append_one
    {seed state nextState : C17KState} {step : Nat}
    (hiter : C17KIter? seed step = some state)
    (hnext : C17KNext? state = some nextState) :
    C17KIter? seed (step + 1) = some nextState := by
  induction step generalizing seed with
  | zero =>
      simp [C17KIter?] at hiter
      cases hiter
      simpa [C17KIter?] using hnext
  | succ step ih =>
      cases hseedNext : C17KNext? seed with
      | none =>
          simp [C17KIter?, hseedNext] at hiter
      | some midState =>
          have htail : C17KIter? midState step = some state := by
            simpa [C17KIter?, hseedNext] using hiter
          have htailNext : C17KIter? midState (step + 1) = some nextState :=
            ih htail
          simpa [C17KIter?, hseedNext] using htailNext
def c17CanonicalLiveBranch (q : Nat) (hodd : q % 2 = 1)
    (seed : C17KState) : C17ActiveLiveBranch :=
  { sourceOdd := q
    sourceOdd_odd := hodd
    liveAt := fun step => ∃ state, C17KIter? seed step = some state
    projectedK := fun step =>
      match C17KIter? seed step with
      | some state => state
      | none => seed }
theorem c17_canonical_branch_projects_at_iter
    {q : Nat} {hodd : q % 2 = 1} {seed state : C17KState} {step : Nat}
    (hiter : C17KIter? seed step = some state) :
    C17BranchProjectsToKAt
      (c17CanonicalLiveBranch q hodd seed) step state := by
  unfold C17BranchProjectsToKAt c17CanonicalLiveBranch
  exact ⟨⟨state, hiter⟩, by simp [hiter]⟩
theorem c17_canonical_branch_follows_kstep
    {q : Nat} {hodd : q % 2 = 1} {seed : C17KState} :
    C17BranchFollowsKStep (c17CanonicalLiveBranch q hodd seed) := by
  intro step state nextState hproject hnext
  obtain ⟨⟨actualState, hiterActual⟩, hprojected⟩ := hproject
  have hactual_eq : actualState = state := by
    unfold c17CanonicalLiveBranch at hprojected
    simpa [hiterActual] using hprojected
  subst actualState
  have hiterNext : C17KIter? seed (step + 1) = some nextState := by
    exact c17_kiter_append_one hiterActual hnext
  exact c17_canonical_branch_projects_at_iter hiterNext
theorem c17_initial_kstate_reachable
    {q : Nat} {seed : C17KState}
    (hodd : q % 2 = 1)
    (_hseed : c17InitialKState? q = some seed) :
    C17ReachableKState seed := by
  refine ⟨c17CanonicalLiveBranch q hodd seed, 0, ?_⟩
  exact c17_canonical_branch_projects_at_iter (seed := seed) (state := seed)
    (step := 0) rfl
theorem c17_initial_kstate_reachable_of_odd
    {q : Nat} {seed : C17KState}
    (hodd : Odd q)
    (hseed : c17InitialKState? q = some seed) :
    C17ReachableKState seed := by
  exact c17_initial_kstate_reachable (Nat.odd_iff.mp hodd) hseed
theorem c17_initial_kstate_following
    {q : Nat} {seed : C17KState}
    (hodd : q % 2 = 1)
    (hseed : c17InitialKState? q = some seed) :
    C17ReachableKStateFollowing seed := by
  exact ⟨q, hodd, seed, 0, hseed, rfl⟩
theorem c17_initial_kstate_following_of_odd
    {q : Nat} {seed : C17KState}
    (hodd : Odd q)
    (hseed : c17InitialKState? q = some seed) :
    C17ReachableKStateFollowing seed := by
  exact c17_initial_kstate_following (Nat.odd_iff.mp hodd) hseed
theorem c17_reachable_following_to_reachable
    {state : C17KState}
    (hreachable : C17ReachableKStateFollowing state) :
    C17ReachableKState state := by
  obtain ⟨q, hodd, seed, step, _hseed, hiter⟩ := hreachable
  exact ⟨c17CanonicalLiveBranch q hodd seed, step,
    c17_canonical_branch_projects_at_iter (q := q) (hodd := hodd)
      (seed := seed) (state := state) (step := step) hiter⟩
theorem c17_reachable_kstate_forward_invariant
    {state nextState : C17KState}
    (hreachable : C17ReachableKState state)
    (hnext : C17KNext? state = some nextState)
    (hfollows :
      ∀ branch step,
        C17BranchProjectsToKAt branch step state ->
          C17BranchFollowsKStep branch) :
    C17ReachableKState nextState := by
  obtain ⟨branch, step, hproject⟩ := hreachable
  exact ⟨branch, step + 1,
    hfollows branch step hproject step state nextState hproject hnext⟩
theorem c17_reachable_kstate_following_forward_invariant
    {state nextState : C17KState}
    (hreachable : C17ReachableKStateFollowing state)
    (hnext : C17KNext? state = some nextState) :
    C17ReachableKStateFollowing nextState := by
  obtain ⟨q, hodd, seed, step, hseed, hiter⟩ := hreachable
  exact ⟨q, hodd, seed, step + 1, hseed,
    c17_kiter_append_one hiter hnext⟩
theorem c17_reachable_kstate_following_iter_forward_invariant
    {state state' : C17KState} {steps : Nat}
    (hreachable : C17ReachableKStateFollowing state)
    (hiter : C17KIter? state steps = some state') :
    C17ReachableKStateFollowing state' := by
  induction steps generalizing state state' with
  | zero =>
      simp [C17KIter?] at hiter
      cases hiter
      exact hreachable
  | succ steps ih =>
      cases hnext : C17KNext? state with
      | none =>
          simp [C17KIter?, hnext] at hiter
      | some midState =>
          have htail : C17KIter? midState steps = some state' := by
            simpa [C17KIter?, hnext] using hiter
          have hmidReachable :
              C17ReachableKStateFollowing midState :=
            c17_reachable_kstate_following_forward_invariant hreachable hnext
          exact ih hmidReachable htail
theorem c17_reachable_kstate_following_valid_pair
    {state : C17KState}
    (hreachable : C17ReachableKStateFollowing state) :
    C17KStateValidPair state := by
  obtain ⟨_q, _hodd, seed, step, hseed, hiter⟩ := hreachable
  exact c17_kiter_valid_pair_of_initial
    (c17_initial_kstate_valid_pair hseed) hiter
def C17KExitsDetectorAt (state : C17KState) (step : Nat) : Prop :=
  ∃ stateAtStep : C17KState,
    C17KIter? state step = some stateAtStep ∧
      (c17L1ClassIsExit (c17L1Class (c17KBreakState stateAtStep)) = true ∨
        C17KNext? stateAtStep = none)
def C17KEntersCycle (state : C17KState) : Prop :=
  ∃ i j : Nat,
  ∃ stateI stateJ : C17KState,
    i < j ∧
      C17KIter? state i = some stateI ∧
      C17KIter? state j = some stateJ ∧
      stateI = stateJ
def c17BoolIndex (b : Bool) : Nat :=
  if b then 1 else 0
theorem c17BoolIndex_lt_two (b : Bool) :
    c17BoolIndex b < 2 := by
  cases b <;> simp [c17BoolIndex]
theorem c17_coarse_pair_label_lt_four (pair : C17CoarsePair) :
    pair.label < 4 := by
  cases pair <;> simp [C17CoarsePair.label]
theorem c17_knext_pairLabel_lt_four
    {state state' : C17KState} (hnext : C17KNext? state = some state') :
    state'.pairLabel < 4 := by
  obtain ⟨pair, _hpair, hlabel⟩ := c17_knext_valid_pair hnext
  rw [hlabel]
  exact c17_coarse_pair_label_lt_four pair
def c17KStateIndex (state : C17KState) : Nat :=
  state.centeredC * 8 + c17BoolIndex state.tParity * 4 + state.pairLabel
theorem c17_kstate_index_lt
    (state : C17KState) (hpair : state.pairLabel < 4) :
    c17KStateIndex state < 3 ^ 17 * 8 := by
  unfold c17KStateIndex
  have hparity := c17BoolIndex_lt_two state.tParity
  have hC := state.centeredC_lt
  omega
theorem c17_kstate_ext
    {state₁ state₂ : C17KState}
    (hC : state₁.centeredC = state₂.centeredC)
    (hT : state₁.tParity = state₂.tParity)
    (hP : state₁.pairLabel = state₂.pairLabel) :
    state₁ = state₂ := by
  cases state₁
  cases state₂
  simp only at hC hT hP
  subst hC
  subst hT
  subst hP
  rfl
theorem c17_odd_state_exits_detector_of_bool
    {state : C17KState}
    (hvalid : C17KStateValidPair state)
    (ht : state.tParity = true)
    (h : c17OddCenteredExitsDetectorBool state.centeredC = true) :
    C17KExitsDetectorAt state 0 := by
  obtain ⟨pair, hpair, hlabel⟩ := hvalid
  unfold c17OddCenteredExitsDetectorBool at h
  split at h
  next hcentered =>
    rw [ht] at hpair
    rw [hpair] at h
    simp only at h
    let boolState : C17KState :=
      { centeredC := state.centeredC
        tParity := true
        pairLabel := pair.label
        centeredC_lt := hcentered }
    have hstateEq : boolState = state := by
      exact c17_kstate_ext rfl ht.symm hlabel.symm
    change
      (c17L1ClassIsExit (c17L1Class (c17KBreakState boolState)) ||
        (C17KNext? boolState).isNone) = true at h
    rw [hstateEq] at h
    refine ⟨state, rfl, ?_⟩
    simp only [Bool.or_eq_true] at h
    rcases h with hexit | hnone
    · exact Or.inl hexit
    · exact Or.inr (Option.isNone_iff_eq_none.mp hnone)
  next hcentered =>
    exact False.elim (hcentered state.centeredC_lt)
theorem c17_even_successor_state_exits_detector_of_bool
    {oddState evenState : C17KState}
    (ht : oddState.tParity = true)
    (hnext : C17KNext? oddState = some evenState)
    (h : c17EvenSuccessorExitsDetectorBool oddState.centeredC = true) :
    C17KExitsDetectorAt oddState 1 := by
  have hcoords := c17_knext_coordinates hnext
  have hvalidEven := c17_knext_valid_pair hnext
  obtain ⟨pair, hpair, hlabel⟩ := hvalidEven
  unfold c17EvenSuccessorExitsDetectorBool at h
  have hnextBound : c17CenteredNext oddState.centeredC < 3 ^ 17 := by
    rw [← hcoords.1]
    exact evenState.centeredC_lt
  have hparityEven : evenState.tParity = false := by
    rw [hcoords.2, ht]
    rfl
  dsimp only at h
  split at h
  next hnextBound' =>
    rw [hcoords.1, hparityEven] at hpair
    rw [hpair] at h
    simp only at h
    let boolState : C17KState :=
      { centeredC := c17CenteredNext oddState.centeredC
        tParity := false
        pairLabel := pair.label
        centeredC_lt := hnextBound' }
    have hstateEq : boolState = evenState := by
      exact c17_kstate_ext hcoords.1.symm hparityEven.symm hlabel.symm
    change
      (c17L1ClassIsExit (c17L1Class (c17KBreakState boolState)) ||
        (C17KNext? boolState).isNone) = true at h
    rw [hstateEq] at h
    refine ⟨evenState, by simp [C17KIter?, hnext], ?_⟩
    simp only [Bool.or_eq_true] at h
    rcases h with hexit | hnone
    · exact Or.inl hexit
    · exact Or.inr (Option.isNone_iff_eq_none.mp hnone)
  next hnextBound' =>
    exact False.elim (hnextBound' hnextBound)
theorem c17_kstate_index_inj
    {state₁ state₂ : C17KState}
    (hpair₁ : state₁.pairLabel < 4)
    (hpair₂ : state₂.pairLabel < 4)
    (hindex : c17KStateIndex state₁ = c17KStateIndex state₂) :
    state₁ = state₂ := by
  unfold c17KStateIndex at hindex
  have hparity₁ := c17BoolIndex_lt_two state₁.tParity
  have hparity₂ := c17BoolIndex_lt_two state₂.tParity
  have hC₁ := state₁.centeredC_lt
  have hC₂ := state₂.centeredC_lt
  have hC : state₁.centeredC = state₂.centeredC := by omega
  have hParityIndex :
      c17BoolIndex state₁.tParity = c17BoolIndex state₂.tParity := by omega
  have hT : state₁.tParity = state₂.tParity := by
    cases h₁ : state₁.tParity <;> cases h₂ : state₂.tParity
    · rfl
    · simp [c17BoolIndex, h₁, h₂] at hParityIndex
    · simp [c17BoolIndex, h₁, h₂] at hParityIndex
    · rfl
  have hP : state₁.pairLabel = state₂.pairLabel := by omega
  exact c17_kstate_ext hC hT hP
theorem c17_orbit_total_of_no_exit
    (state : C17KState)
    (hnoExit : ∀ step, ¬ C17KExitsDetectorAt state step) :
    ∀ step, ∃ stateAtStep : C17KState,
      C17KIter? state step = some stateAtStep := by
  intro step
  induction step generalizing state with
  | zero =>
      exact ⟨state, rfl⟩
  | succ step ih =>
      have hnextExists : ∃ nextState, C17KNext? state = some nextState := by
        cases hnext : C17KNext? state with
        | none =>
            exfalso
            exact hnoExit 0 ⟨state, rfl, Or.inr hnext⟩
        | some nextState =>
            exact ⟨nextState, by simp⟩
      obtain ⟨nextState, hnext⟩ := hnextExists
      have hnoExitNext : ∀ step, ¬ C17KExitsDetectorAt nextState step := by
        intro step' hexit
        obtain ⟨exitState, hiter, hnone⟩ := hexit
        exact hnoExit (step' + 1)
          ⟨exitState,
            by rw [c17_kiter_succ_some state nextState step' hnext]; exact hiter,
            hnone⟩
      obtain ⟨stateAtStep, hiter⟩ := ih nextState hnoExitNext
      exact ⟨stateAtStep,
        by rw [c17_kiter_succ_some state nextState step hnext]; exact hiter⟩
theorem c17_iter_pairLabel_lt_four_after_success
    {state stateAtStep : C17KState} {step : Nat}
    (hiter : C17KIter? state (step + 1) = some stateAtStep) :
    stateAtStep.pairLabel < 4 := by
  induction step generalizing state stateAtStep with
  | zero =>
      cases hnext : C17KNext? state with
      | none =>
          simp [C17KIter?, hnext] at hiter
      | some nextState =>
          simp [C17KIter?, hnext] at hiter
          cases hiter
          exact c17_knext_pairLabel_lt_four hnext
  | succ step ih =>
      cases hnext : C17KNext? state with
      | none =>
          simp [C17KIter?, hnext] at hiter
      | some nextState =>
          have htail : C17KIter? nextState (step + 1) = some stateAtStep := by
            simpa [C17KIter?, hnext] using hiter
          exact ih htail
theorem c17_pigeonhole :
    ∀ (N : Nat) (f : Nat -> Nat),
      0 < N ->
      (∀ i, i <= N -> f i < N) ->
      ∃ i j, i < j ∧ j <= N ∧ f i = f j := by
  intro N
  induction N with
  | zero =>
      intro f hpos _hbound
      omega
  | succ k ih =>
      intro f _hpos hbound
      by_cases hcollideLast : ∃ i, i <= k ∧ f i = f (k + 1)
      · obtain ⟨i, hi, heq⟩ := hcollideLast
        exact ⟨i, k + 1, by omega, by omega, heq⟩
      · have hnotLast : ∀ i, i <= k -> f i ≠ f (k + 1) := by
          intro i hi heq
          exact hcollideLast ⟨i, hi, heq⟩
        cases k with
        | zero =>
            have h0 : f 0 < 1 := hbound 0 (by omega)
            have h1 : f 1 < 1 := hbound 1 (by omega)
            exact ⟨0, 1, by omega, by omega, by omega⟩
        | succ k' =>
            let g : Nat -> Nat := fun i =>
              if f i < f (k' + 2) then f i else f i - 1
            have hgBound : ∀ i, i <= k' + 1 -> g i < k' + 1 := by
              intro i hi
              have hfi : f i < k' + 2 := hbound i (by omega)
              have hfk : f (k' + 2) < k' + 2 := hbound (k' + 2) (by omega)
              have hne : f i ≠ f (k' + 2) := hnotLast i (by omega)
              unfold g
              split <;> omega
            obtain ⟨i, j, hij, hj, hgij⟩ := ih g (by omega) hgBound
            have hni : f i ≠ f (k' + 2) := hnotLast i (by omega)
            have hnj : f j ≠ f (k' + 2) := hnotLast j (by omega)
            unfold g at hgij
            refine ⟨i, j, hij, by omega, ?_⟩
            split at hgij <;> split at hgij <;> omega
theorem c17_korbit_exit_or_cycle
    (state : C17KState) :
    (∃ step, C17KExitsDetectorAt state step) ∨ C17KEntersCycle state := by
  by_cases hexit : ∃ step, C17KExitsDetectorAt state step
  · exact Or.inl hexit
  · have hnoExit : ∀ step, ¬ C17KExitsDetectorAt state step := by
      simpa [not_exists] using hexit
    have htotal := c17_orbit_total_of_no_exit state hnoExit
    let f : Nat -> Nat := fun i =>
      c17KStateIndex ((htotal (i + 1)).choose)
    have hfSpec :
        ∀ i, C17KIter? state (i + 1) = some ((htotal (i + 1)).choose) := by
      intro i
      exact (htotal (i + 1)).choose_spec
    have hfBound : ∀ i, i <= 3 ^ 17 * 8 -> f i < 3 ^ 17 * 8 := by
      intro i _hi
      unfold f
      exact c17_kstate_index_lt ((htotal (i + 1)).choose)
        (c17_iter_pairLabel_lt_four_after_success (hfSpec i))
    have hNpos : 0 < 3 ^ 17 * 8 := by norm_num
    obtain ⟨i, j, hij, _hj, hindex⟩ :=
      c17_pigeonhole (3 ^ 17 * 8) f hNpos hfBound
    have hiterI := hfSpec i
    have hiterJ := hfSpec j
    have hpairI :=
      c17_iter_pairLabel_lt_four_after_success hiterI
    have hpairJ :=
      c17_iter_pairLabel_lt_four_after_success hiterJ
    have hstateEq :
        (htotal (i + 1)).choose = (htotal (j + 1)).choose :=
      c17_kstate_index_inj hpairI hpairJ hindex
    exact Or.inr
      ⟨i + 1, j + 1, (htotal (i + 1)).choose, (htotal (j + 1)).choose,
        by omega, hiterI, hiterJ, hstateEq⟩
theorem c17_reachable_exit_state_of_exits_detector
    {state : C17KState} {step : Nat}
    (hreachable : C17ReachableKStateFollowing state)
    (hexit : C17KExitsDetectorAt state step) :
    ∃ exitState : C17KState,
      C17ReachableKStateFollowing exitState ∧
        C17KIter? state step = some exitState ∧
        (c17L1ClassIsExit (c17L1Class (c17KBreakState exitState)) = true ∨
          C17KNext? exitState = none) := by
  obtain ⟨exitState, hiter, hexitStop⟩ := hexit
  exact ⟨exitState,
    c17_reachable_kstate_following_iter_forward_invariant hreachable hiter,
    hiter,
    hexitStop⟩
theorem c17_reachable_cycle_states_of_enters_cycle
    {state : C17KState}
    (hreachable : C17ReachableKStateFollowing state)
    (hcycle : C17KEntersCycle state) :
    ∃ i j : Nat,
    ∃ stateI stateJ : C17KState,
      i < j ∧
        C17ReachableKStateFollowing stateI ∧
        C17ReachableKStateFollowing stateJ ∧
        C17KIter? state i = some stateI ∧
        C17KIter? state j = some stateJ ∧
        stateI = stateJ := by
  obtain ⟨i, j, stateI, stateJ, hij, hI, hJ, hEq⟩ := hcycle
  exact ⟨i, j, stateI, stateJ,
    hij,
    c17_reachable_kstate_following_iter_forward_invariant hreachable hI,
    c17_reachable_kstate_following_iter_forward_invariant hreachable hJ,
    hI,
    hJ,
    hEq⟩
theorem c17_kiter_add :
    ∀ (first second : Nat) (state : C17KState),
      C17KIter? state (first + second) =
        (C17KIter? state first).bind
          (fun state' => C17KIter? state' second)
  | 0, second, state => by
      simp [C17KIter?]
  | first + 1, second, state => by
      rw [Nat.succ_add]
      cases hnext : C17KNext? state with
      | none =>
          rw [c17_kiter_succ_none state (first + second) hnext]
          rw [c17_kiter_succ_none state first hnext]
          rfl
      | some nextState =>
          rw [c17_kiter_succ_some state nextState (first + second) hnext]
          rw [c17_kiter_succ_some state nextState first hnext]
          exact c17_kiter_add first second nextState
theorem c17_kexit_after_prefix
    {seed state : C17KState} {entryStep exitStep : Nat}
    (hentry : C17KIter? seed entryStep = some state)
    (hexit : C17KExitsDetectorAt state exitStep) :
    C17KExitsDetectorAt seed (entryStep + exitStep) := by
  obtain ⟨exitState, hiter, hexitStop⟩ := hexit
  refine ⟨exitState, ?_, hexitStop⟩
  have hadd := c17_kiter_add entryStep exitStep seed
  rw [hentry] at hadd
  exact hadd.trans hiter
theorem c17_odd_state_next_exists_of_odd_exit_bool_false
    {state : C17KState}
    (hvalid : C17KStateValidPair state)
    (ht : state.tParity = true)
    (hodd : c17OddCenteredExitsDetectorBool state.centeredC = false) :
    ∃ evenState : C17KState, C17KNext? state = some evenState := by
  cases hnext : C17KNext? state with
  | none =>
      exfalso
      obtain ⟨pair, hpair, hlabel⟩ := hvalid
      unfold c17OddCenteredExitsDetectorBool at hodd
      rw [dif_pos state.centeredC_lt] at hodd
      rw [ht] at hpair
      rw [hpair] at hodd
      simp only at hodd
      let boolState : C17KState :=
        { centeredC := state.centeredC
          tParity := true
          pairLabel := pair.label
          centeredC_lt := state.centeredC_lt }
      have hstateEq : boolState = state := by
        exact c17_kstate_ext rfl ht.symm hlabel.symm
      change
        (c17L1ClassIsExit (c17L1Class (c17KBreakState boolState)) ||
          (C17KNext? boolState).isNone) = false at hodd
      rw [hstateEq, hnext] at hodd
      simp at hodd
  | some evenState =>
      exact ⟨evenState, rfl⟩
theorem c17_even_successor_next_exists_of_even_exit_bool_false
    {oddState evenState : C17KState}
    (ht : oddState.tParity = true)
    (hnext : C17KNext? oddState = some evenState)
    (heven : c17EvenSuccessorExitsDetectorBool oddState.centeredC = false) :
    ∃ nextOddState : C17KState, C17KNext? evenState = some nextOddState := by
  cases hnext2 : C17KNext? evenState with
  | none =>
      exfalso
      have hcoords := c17_knext_coordinates hnext
      have hvalidEven := c17_knext_valid_pair hnext
      obtain ⟨pair, hpair, hlabel⟩ := hvalidEven
      have hnextBound : c17CenteredNext oddState.centeredC < 3 ^ 17 := by
        rw [← hcoords.1]
        exact evenState.centeredC_lt
      have hparityEven : evenState.tParity = false := by
        rw [hcoords.2, ht]
        rfl
      unfold c17EvenSuccessorExitsDetectorBool at heven
      rw [dif_pos hnextBound] at heven
      rw [hcoords.1, hparityEven] at hpair
      rw [hpair] at heven
      simp only at heven
      let boolState : C17KState :=
        { centeredC := c17CenteredNext oddState.centeredC
          tParity := false
          pairLabel := pair.label
          centeredC_lt := hnextBound }
      have hstateEq : boolState = evenState := by
        exact c17_kstate_ext hcoords.1.symm hparityEven.symm hlabel.symm
      change
        (c17L1ClassIsExit (c17L1Class (c17KBreakState boolState)) ||
          (C17KNext? boolState).isNone) = false at heven
      rw [hstateEq, hnext2] at heven
      simp at heven
  | some nextOddState =>
      exact ⟨nextOddState, rfl⟩
theorem c17_two_step_odd_state_of_no_detector_bools
    {state : C17KState}
    (hvalid : C17KStateValidPair state)
    (ht : state.tParity = true)
    (hodd : c17OddCenteredExitsDetectorBool state.centeredC = false)
    (heven : c17EvenSuccessorExitsDetectorBool state.centeredC = false) :
    ∃ nextOddState : C17KState,
      C17KIter? state 2 = some nextOddState ∧
        nextOddState.tParity = true ∧
        nextOddState.centeredC = c17TwoStepOddCentered state.centeredC ∧
        C17KStateValidPair nextOddState := by
  obtain ⟨evenState, hnext⟩ :=
    c17_odd_state_next_exists_of_odd_exit_bool_false hvalid ht hodd
  obtain ⟨nextOddState, hnext2⟩ :=
    c17_even_successor_next_exists_of_even_exit_bool_false ht hnext heven
  have hcoords := c17_knext_coordinates hnext
  have hcoords2 := c17_knext_coordinates hnext2
  refine ⟨nextOddState, ?_, ?_, ?_, c17_knext_valid_pair hnext2⟩
  · simp [C17KIter?, hnext, hnext2]
  · rw [hcoords2.2, hcoords.2, ht]
    rfl
  · simp [c17TwoStepOddCentered, hcoords.1, hcoords2.1]
theorem c17_exit_of_even_successor_bool
    {oddState : C17KState}
    (ht : oddState.tParity = true)
    (heven : c17EvenSuccessorExitsDetectorBool oddState.centeredC = true) :
    ∃ step : Nat, C17KExitsDetectorAt oddState step := by
  cases hnext : C17KNext? oddState with
  | none =>
      exact ⟨0, oddState, rfl, Or.inr hnext⟩
  | some evenState =>
      exact ⟨1,
        c17_even_successor_state_exits_detector_of_bool ht hnext heven⟩
theorem c17_detector_exit_of_odd_centered_cycle_scan
    {state : C17KState} {fuel start : Nat}
    (hvalid : C17KStateValidPair state)
    (ht : state.tParity = true)
    (hscan :
      c17OddCenteredCycleHasDetectorExit fuel start state.centeredC = true) :
    ∃ step : Nat, C17KExitsDetectorAt state step := by
  induction fuel generalizing state with
  | zero =>
      cases hscan
  | succ fuel ih =>
      cases hodd :
          c17OddCenteredExitsDetectorBool state.centeredC
      · cases heven :
            c17EvenSuccessorExitsDetectorBool state.centeredC
        · simp [c17OddCenteredCycleHasDetectorExit, hodd, heven] at hscan
          obtain ⟨_hnotStart, hscanTail⟩ := hscan
          obtain ⟨nextOddState, hiter2, htNext, hCNext, hvalidNext⟩ :=
            c17_two_step_odd_state_of_no_detector_bools
              hvalid ht hodd heven
          have hscanNext :
              c17OddCenteredCycleHasDetectorExit fuel start
                nextOddState.centeredC = true := by
            rw [hCNext]
            exact hscanTail
          obtain ⟨exitStep, hexit⟩ := ih hvalidNext htNext hscanNext
          exact ⟨2 + exitStep,
            c17_kexit_after_prefix hiter2 hexit⟩
        · exact c17_exit_of_even_successor_bool ht heven
      · exact ⟨0, c17_odd_state_exits_detector_of_bool hvalid ht hodd⟩
theorem c17_odd_state_reaches_two_step_iter_or_exits
    {state : C17KState} (steps : Nat)
    (hvalid : C17KStateValidPair state)
    (ht : state.tParity = true) :
    (∃ exitStep : Nat, C17KExitsDetectorAt state exitStep) ∨
      ∃ stateAt : C17KState,
        C17KIter? state (2 * steps) = some stateAt ∧
          stateAt.tParity = true ∧
          stateAt.centeredC =
            (c17TwoStepOddCentered^[steps]) state.centeredC ∧
          C17KStateValidPair stateAt := by
  induction steps generalizing state with
  | zero =>
      exact Or.inr ⟨state, by simp [C17KIter?], ht, by simp, hvalid⟩
  | succ steps ih =>
      cases hodd : c17OddCenteredExitsDetectorBool state.centeredC
      · cases heven : c17EvenSuccessorExitsDetectorBool state.centeredC
        · obtain ⟨nextOddState, hiter2, htNext, hCNext, hvalidNext⟩ :=
            c17_two_step_odd_state_of_no_detector_bools hvalid ht hodd heven
          rcases ih hvalidNext htNext with hexit | htail
          · exact Or.inl
              ⟨2 + hexit.choose,
                c17_kexit_after_prefix hiter2 hexit.choose_spec⟩
          · obtain ⟨stateAt, hiterTail, htAt, hCAt, hvalidAt⟩ := htail
            refine Or.inr ⟨stateAt, ?_, ?_, ?_, ?_⟩
            · have hadd := c17_kiter_add 2 (2 * steps) state
              rw [hiter2] at hadd
              simp [hiterTail] at hadd
              have hsteps : 2 * (steps + 1) = 2 + 2 * steps := by omega
              rw [hsteps]
              exact hadd
            · exact htAt
            · rw [Function.iterate_succ_apply]
              rw [← hCNext]
              exact hCAt
            · exact hvalidAt
        · exact Or.inl (c17_exit_of_even_successor_bool ht heven)
      · exact Or.inl
          ⟨0, c17_odd_state_exits_detector_of_bool hvalid ht hodd⟩
theorem c17_detector_exit_of_odd_representative
    {state : C17KState}
    (hvalid : C17KStateValidPair state)
    (ht : state.tParity = true)
    (hrep :
      state.centeredC = 1 ∨ state.centeredC = 4 ∨ state.centeredC = 7) :
    ∃ step : Nat, C17KExitsDetectorAt state step := by
  rcases hrep with h1 | h4 | h7
  · exact c17_detector_exit_of_odd_centered_cycle_scan hvalid ht
      (by simpa [h1] using c17_odd_centered_cycle_scan_one_true)
  · exact c17_detector_exit_of_odd_centered_cycle_scan hvalid ht
      (by simpa [h4] using c17_odd_centered_cycle_scan_four_true)
  · exact c17_detector_exit_of_odd_centered_cycle_scan hvalid ht
      (by simpa [h7] using c17_odd_centered_cycle_scan_seven_true)
def C17ReachableCycleWitnessInRK (seed : C17KState) : Prop :=
  ∃ recurrentState : C17KState,
  ∃ entryStep period : Nat,
    C17KIter? seed entryStep = some recurrentState ∧
      C17ReachableKStateFollowing recurrentState ∧
      0 < period ∧
      C17KIter? recurrentState period = some recurrentState
theorem c17_reachable_cycle_witness_in_rk_of_cycle
    {state : C17KState}
    (hreachable : C17ReachableKStateFollowing state)
    (hcycle : C17KEntersCycle state) :
    C17ReachableCycleWitnessInRK state := by
  obtain ⟨i, j, stateI, stateJ, hij, hI, hJ, hEq⟩ := hcycle
  refine ⟨stateI, i, j - i, hI, ?_, by omega, ?_⟩
  · exact c17_reachable_kstate_following_iter_forward_invariant hreachable hI
  · have hadd := c17_kiter_add i (j - i) state
    have hji : i + (j - i) = j := by omega
    rw [hji, hJ, hI] at hadd
    have hperiod : C17KIter? stateI (j - i) = some stateJ := hadd.symm
    rw [hperiod, hEq]
theorem c17_korbit_break_value
    (seed : C17KState) (step : Nat) (stateAtStep : C17KState)
    (hiter : C17KIter? seed step = some stateAtStep) :
    c17KBreakState stateAtStep =
      c17KBreakState
        { centeredC := c17CenteredNextIter step seed.centeredC
          tParity := if step % 2 = 0 then seed.tParity else !seed.tParity
          pairLabel := stateAtStep.pairLabel
          centeredC_lt := by
            rw [← (c17_korbit_tracks_break_coordinates seed step stateAtStep hiter).1]
            exact stateAtStep.centeredC_lt } := by
  obtain ⟨hC, hP⟩ := c17_korbit_tracks_break_coordinates seed step stateAtStep hiter
  unfold c17KBreakState
  simp [hC, hP]
theorem c17_initial_kstate_break_state
    (q : Nat) (hodd : q % 2 = 1)
    {seed : C17KState}
    (hseed : c17InitialKState? q = some seed) :
    c17KBreakState seed = q % c17CenteredA := by
  unfold c17InitialKState? at hseed
  cases hpair :
      c17PairFromCoarse (c17InitialCentered q % 24) true with
  | none =>
      simp [hpair] at hseed
  | some pair =>
      simp [hpair] at hseed
      cases hseed
      simp [c17KBreakState, c17InitialCentered, c17CenteredA]
      let r := q % 86093442 / 2
      have hmodForm : q % 86093442 = 2 * r + 1 := by
        have hoddMod : q % 86093442 % 2 = 1 := by
          rw [Nat.mod_mod_of_dvd q (by norm_num : 2 ∣ 86093442)]
          exact hodd
        unfold r
        omega
      rw [hmodForm]
      have hdiv : (3 * (2 * r + 1) - 1) / 2 = 3 * r + 1 := by
        have hnum : 3 * (2 * r + 1) - 1 = 2 * (3 * r + 1) := by
          omega
        rw [hnum]
        exact Nat.mul_div_right (3 * r + 1) (by norm_num : 0 < 2)
      rw [hdiv]
      omega
theorem c17_initial_kstate_break_state_of_odd
    (q : Nat) (hodd : Odd q)
    {seed : C17KState}
    (hseed : c17InitialKState? q = some seed) :
    c17KBreakState seed = q % c17CenteredA :=
  c17_initial_kstate_break_state q (Nat.odd_iff.mp hodd) hseed
theorem c17_kstate_mod3_of_valid_pair
    {state : C17KState}
    (hvalid : C17KStateValidPair state) :
    if state.tParity then state.centeredC % 3 = 1
    else state.centeredC % 3 = 2 := by
  obtain ⟨pair, hpair, _hlabel⟩ := hvalid
  let r := state.centeredC % 24
  have hrlt : r < 24 := by
    unfold r
    exact Nat.mod_lt state.centeredC (by omega)
  have hmod3_of_mod24 :
      state.centeredC % 3 = r % 3 := by
    unfold r
    rw [Nat.mod_mod_of_dvd state.centeredC (by norm_num : 3 ∣ 24)]
  have hpairR : c17PairFromCoarse r state.tParity = some pair := by
    simpa [r] using hpair
  cases ht : state.tParity
  · simp
    simp [ht] at hpairR
    interval_cases r <;>
      simp [c17PairFromCoarse] at hpairR <;>
      simp [hmod3_of_mod24]
  · simp
    simp [ht] at hpairR
    interval_cases r <;>
      simp [c17PairFromCoarse] at hpairR <;>
      simp [hmod3_of_mod24]
theorem c17_valid_odd_centered_mod3
    {state : C17KState}
    (hvalid : C17KStateValidPair state)
    (ht : state.tParity = true) :
    state.centeredC % 3 = 1 := by
  have hmod := c17_kstate_mod3_of_valid_pair hvalid
  rw [ht] at hmod
  simpa using hmod
theorem c17_detector_exit_of_valid_odd_state
    {state : C17KState}
    (hvalid : C17KStateValidPair state)
    (ht : state.tParity = true) :
    ∃ step : Nat, C17KExitsDetectorAt state step := by
  have hmod3 := c17_valid_odd_centered_mod3 hvalid ht
  have hcState : Nat.Coprime state.centeredC (3 ^ 17) := by
    have h3c : Nat.Coprime 3 state.centeredC := by
      rw [(by norm_num : Nat.Prime 3).coprime_iff_not_dvd]
      intro hdiv
      have hzero : state.centeredC % 3 = 0 :=
        Nat.mod_eq_zero_of_dvd hdiv
      omega
    have hpow : Nat.Coprime (3 ^ 17) state.centeredC :=
      Nat.Coprime.pow_left 17 h3c
    rwa [Nat.coprime_comm]
  rcases c17_odd_centered_mod9_cases hmod3 with h1 | h4 | h7
  · have hmod : (state.centeredC : ZMod 9) = (1 : ZMod 9) := by
      exact (ZMod.natCast_eq_natCast_iff state.centeredC 1 9).2 (by
        simpa [Nat.ModEq] using h1)
    obtain ⟨n, hn⟩ :=
      c17_two_step_orbit_reaches_representative_of_same_mod9
        state.centeredC_lt (by norm_num : 1 < 3 ^ 17)
        hcState
        (by norm_num : Nat.Coprime 1 (3 ^ 17)) hmod
    rcases c17_odd_state_reaches_two_step_iter_or_exits n hvalid ht with hexit | hreach
    · exact hexit
    · obtain ⟨stateAt, hiter, htAt, hCAt, hvalidAt⟩ := hreach
      have hrepAt : stateAt.centeredC = 1 ∨ stateAt.centeredC = 4 ∨
          stateAt.centeredC = 7 := by
        left
        rw [hCAt, hn]
      obtain ⟨exitStep, hexitAt⟩ :=
        c17_detector_exit_of_odd_representative hvalidAt htAt hrepAt
      exact ⟨2 * n + exitStep,
        c17_kexit_after_prefix hiter hexitAt⟩
  · have hmod : (state.centeredC : ZMod 9) = (4 : ZMod 9) := by
      exact (ZMod.natCast_eq_natCast_iff state.centeredC 4 9).2 (by
        simpa [Nat.ModEq] using h4)
    obtain ⟨n, hn⟩ :=
      c17_two_step_orbit_reaches_representative_of_same_mod9
        state.centeredC_lt (by norm_num : 4 < 3 ^ 17)
        hcState
        (by norm_num : Nat.Coprime 4 (3 ^ 17)) hmod
    rcases c17_odd_state_reaches_two_step_iter_or_exits n hvalid ht with hexit | hreach
    · exact hexit
    · obtain ⟨stateAt, hiter, htAt, hCAt, hvalidAt⟩ := hreach
      have hrepAt : stateAt.centeredC = 1 ∨ stateAt.centeredC = 4 ∨
          stateAt.centeredC = 7 := by
        right
        left
        rw [hCAt, hn]
      obtain ⟨exitStep, hexitAt⟩ :=
        c17_detector_exit_of_odd_representative hvalidAt htAt hrepAt
      exact ⟨2 * n + exitStep,
        c17_kexit_after_prefix hiter hexitAt⟩
  · have hmod : (state.centeredC : ZMod 9) = (7 : ZMod 9) := by
      exact (ZMod.natCast_eq_natCast_iff state.centeredC 7 9).2 (by
        simpa [Nat.ModEq] using h7)
    obtain ⟨n, hn⟩ :=
      c17_two_step_orbit_reaches_representative_of_same_mod9
        state.centeredC_lt (by norm_num : 7 < 3 ^ 17)
        hcState
        (by norm_num : Nat.Coprime 7 (3 ^ 17)) hmod
    rcases c17_odd_state_reaches_two_step_iter_or_exits n hvalid ht with hexit | hreach
    · exact hexit
    · obtain ⟨stateAt, hiter, htAt, hCAt, hvalidAt⟩ := hreach
      have hrepAt : stateAt.centeredC = 1 ∨ stateAt.centeredC = 4 ∨
          stateAt.centeredC = 7 := by
        right
        right
        rw [hCAt, hn]
      obtain ⟨exitStep, hexitAt⟩ :=
        c17_detector_exit_of_odd_representative hvalidAt htAt hrepAt
      exact ⟨2 * n + exitStep,
        c17_kexit_after_prefix hiter hexitAt⟩
theorem c17_detector_exit_of_reachable_cycle
    {state : C17KState}
    (hreachable : C17ReachableKStateFollowing state)
    (hcycle : C17KEntersCycle state) :
    ∃ step : Nat, C17KExitsDetectorAt state step := by
  have hrecurrent : C17ReachableCycleWitnessInRK state :=
    c17_reachable_cycle_witness_in_rk_of_cycle hreachable hcycle
  obtain ⟨recurrentState, entryStep, period, hentry, hreachRec,
    _hperiodPos, _hperiod⟩ := hrecurrent
  have hvalidRec := c17_reachable_kstate_following_valid_pair hreachRec
  cases ht : recurrentState.tParity
  · cases hnext : C17KNext? recurrentState with
    | none =>
        exact ⟨entryStep, recurrentState, hentry, Or.inr hnext⟩
    | some oddState =>
        have hcoords := c17_knext_coordinates hnext
        have htOdd : oddState.tParity = true := by
          rw [hcoords.2, ht]
          rfl
        obtain ⟨exitStep, hexitOdd⟩ :=
          c17_detector_exit_of_valid_odd_state
            (c17_knext_valid_pair hnext) htOdd
        have hentryOdd :
            C17KIter? state (entryStep + 1) = some oddState :=
          c17_kiter_append_one hentry hnext
        exact ⟨entryStep + 1 + exitStep,
          c17_kexit_after_prefix hentryOdd hexitOdd⟩
  · have htOdd : recurrentState.tParity = true := ht
    obtain ⟨exitStep, hexitRec⟩ :=
      c17_detector_exit_of_valid_odd_state hvalidRec htOdd
    exact ⟨entryStep + exitStep,
      c17_kexit_after_prefix hentry hexitRec⟩
theorem c17_reachable_korbit_exits_detector
    {seed : C17KState}
    (hreachable : C17ReachableKStateFollowing seed) :
    ∃ step : Nat, C17KExitsDetectorAt seed step := by
  cases c17_korbit_exit_or_cycle seed with
  | inl hexit =>
      exact hexit
  | inr hcycle =>
      exact c17_detector_exit_of_reachable_cycle hreachable hcycle
private theorem c17_kbreak_state_divisible
    (state : C17KState) (hvalid : C17KStateValidPair state) :
    if state.tParity then (2 * state.centeredC + 1) % 3 = 0
    else (state.centeredC + 1) % 3 = 0 := by
  have hmod3 := c17_kstate_mod3_of_valid_pair hvalid
  cases ht : state.tParity
  · simp [ht] at hmod3 ⊢
    rw [Nat.add_mod, hmod3]
  ·
    simp [ht] at hmod3 ⊢
    rw [Nat.add_mod, Nat.mul_mod, hmod3]
theorem c17_kbreak_state_exact
    (state : C17KState) (hvalid : C17KStateValidPair state) :
    if state.tParity then
      3 * c17KBreakState state = 2 * state.centeredC + 1
    else
      3 * c17KBreakState state = state.centeredC + 1 := by
  have hdiv := c17_kbreak_state_divisible state hvalid
  unfold c17KBreakState
  cases ht : state.tParity
  · simp [ht] at hdiv ⊢
    have hdvd : 3 ∣ state.centeredC + 1 :=
      Nat.dvd_of_mod_eq_zero hdiv
    have hmul := Nat.div_mul_cancel hdvd
    omega
  ·
    simp [ht] at hdiv ⊢
    have hdvd : 3 ∣ 2 * state.centeredC + 1 :=
      Nat.dvd_of_mod_eq_zero hdiv
    have hmul := Nat.div_mul_cancel hdvd
    omega
theorem c17_knext_break_step_odd
    {state nextState : C17KState}
    (hvalid : C17KStateValidPair state)
    (hnext : C17KNext? state = some nextState)
    (ht : state.tParity = true) :
    16 * c17KBreakState nextState =
      c17KBreakState state + 5 +
        c17CenteredA * c17SurvivorResidue (state.centeredC % 8) := by
  have hnextCoords := c17_knext_coordinates hnext
  have hnextValid := c17_knext_valid_pair hnext
  have hB := c17_kbreak_state_exact state hvalid
  have hB' := c17_kbreak_state_exact nextState hnextValid
  rw [ht] at hB
  simp at hB
  have htNext : nextState.tParity = false := by
    rw [hnextCoords.2, ht]
    rfl
  rw [htNext] at hB'
  simp at hB'
  have hnumer := c17_centered_numer_eq_eight_mul_next state.centeredC
  have hCnext : nextState.centeredC = c17CenteredNext state.centeredC :=
    hnextCoords.1
  rw [← hCnext] at hnumer
  unfold c17CenteredA c17CenteredD at *
  omega
theorem c17_knext_break_step_even
    {state nextState : C17KState}
    (hvalid : C17KStateValidPair state)
    (hnext : C17KNext? state = some nextState)
    (ht : state.tParity = false) :
    12 * c17KBreakState nextState =
      3 * c17KBreakState state + 3 +
        c17CenteredD * c17SurvivorResidue (state.centeredC % 8) := by
  have hnextCoords := c17_knext_coordinates hnext
  have hnextValid := c17_knext_valid_pair hnext
  have hB := c17_kbreak_state_exact state hvalid
  have hB' := c17_kbreak_state_exact nextState hnextValid
  rw [ht] at hB
  simp at hB
  have htNext : nextState.tParity = true := by
    rw [hnextCoords.2, ht]
    rfl
  rw [htNext] at hB'
  simp at hB'
  have hnumer := c17_centered_numer_eq_eight_mul_next state.centeredC
  have hCnext : nextState.centeredC = c17CenteredNext state.centeredC :=
    hnextCoords.1
  rw [← hCnext] at hnumer
  unfold c17CenteredD at *
  omega
def c17KFirstHitGlobalEntryRow (q : Nat) : C17Lemma1aGlobalEntryRow :=
  if q == 1 || q == 3 || q == 15 || q == 39 ||
      q == 6651 || q == 70939 || q == 378341 then
    C17Lemma1aGlobalEntryRow.finiteFunnel
  else if q % 6 == 1 || q % 6 == 3 then
    C17Lemma1aGlobalEntryRow.baseTemplates
  else if q % 128 == 85 then
    C17Lemma1aGlobalEntryRow.finiteSplice128u85
  else if q % 32 == 5 then
    C17Lemma1aGlobalEntryRow.fixedQ5Mod32Layer
  else if q % 16 == 5 then
    C17Lemma1aGlobalEntryRow.sectorQ5Mod16
  else if q % 486 == 425 then
    C17Lemma1aGlobalEntryRow.continuation425486u
  else if q % 486 == 59 || q % 486 == 79 || q % 486 == 25 then
    C17Lemma1aGlobalEntryRow.normalizedSuccessors597925486u
  else if q < 2048 then
    C17Lemma1aGlobalEntryRow.boundedSinksQLt2048
  else if q == 4597 || q == 5029 then
    C17Lemma1aGlobalEntryRow.exceptionalTargets45975029
  else if q % 64 == 43 then
    C17Lemma1aGlobalEntryRow.directDescent43Mod64
  else
    C17Lemma1aGlobalEntryRow.recordedTerminalDownstreamStock
theorem c17_kexit_to_global_entry_row
    {seed exitState : C17KState} {step : Nat}
    (_hiter : C17KIter? seed step = some exitState)
    (_hexitStop :
      c17L1ClassIsExit (c17L1Class (c17KBreakState exitState)) = true ∨
        C17KNext? exitState = none) :
    ∃ row : C17Lemma1aGlobalEntryRow,
      row ∈ c17Lemma1aGlobalEntryRows ∧
        (C17Lemma1aImmediateCloseoutRow row ∨
          C17Lemma1aFixedEntryRow row ∨
          C17Lemma1aFiniteLaunchMenuRow row ∨
          C17Lemma1aDownstreamCarrierRow row) ∧
        row = c17KFirstHitGlobalEntryRow (c17KBreakState exitState) := by
  let row := c17KFirstHitGlobalEntryRow (c17KBreakState exitState)
  refine ⟨row, c17_lemma1a_global_entry_rows_complete row, ?_, rfl⟩
  exact c17_global_entry_row_enters_bucket row
theorem c17_kexit_witness_to_global_entry_row
    {seed : C17KState} {step : Nat}
    (hexit : C17KExitsDetectorAt seed step) :
    ∃ exitState : C17KState,
    ∃ row : C17Lemma1aGlobalEntryRow,
      C17KIter? seed step = some exitState ∧
        (c17L1ClassIsExit (c17L1Class (c17KBreakState exitState)) = true ∨
          C17KNext? exitState = none) ∧
        row ∈ c17Lemma1aGlobalEntryRows ∧
        (C17Lemma1aImmediateCloseoutRow row ∨
          C17Lemma1aFixedEntryRow row ∨
          C17Lemma1aFiniteLaunchMenuRow row ∨
          C17Lemma1aDownstreamCarrierRow row) ∧
        row = c17KFirstHitGlobalEntryRow (c17KBreakState exitState) := by
  obtain ⟨exitState, hiter, hexitStop⟩ := hexit
  obtain ⟨row, hmem, hbucket, hrow⟩ :=
    c17_kexit_to_global_entry_row hiter hexitStop
  exact ⟨exitState, row, hiter, hexitStop, hmem, hbucket, hrow⟩
def C17KOrbitC10Faithfulness : Prop :=
  ∀ {q : Nat} {seed state : C17KState} {step : Nat},
    Odd q ->
      c17InitialKState? q = some seed ->
        C17KIter? seed step = some state ->
          state.centeredC = c17CenteredNextIter step seed.centeredC ∧
            state.tParity =
              (if step % 2 = 0 then seed.tParity else !seed.tParity) ∧
            C17ReachableKState state
theorem c17_k_orbit_c10_faithfulness :
    C17KOrbitC10Faithfulness := by
  intro q seed state step hodd hseed hiter
  have hcoords := c17_korbit_tracks_break_coordinates seed step state hiter
  have hreachable : C17ReachableKState state :=
    ⟨c17CanonicalLiveBranch q (Nat.odd_iff.mp hodd) seed, step,
      c17_canonical_branch_projects_at_iter (q := q)
        (hodd := Nat.odd_iff.mp hodd) (seed := seed) (state := state)
        (step := step) hiter⟩
  exact ⟨hcoords.1, hcoords.2, hreachable⟩
inductive C17Lemma1aReachabilityCover (q : Nat) : Prop where
  | detectorExit
      {seed exitState : C17KState} {step : Nat}
      (hseed : c17InitialKState? q = some seed)
      (hiter : C17KIter? seed step = some exitState)
      (hexitStop :
        c17L1ClassIsExit (c17L1Class (c17KBreakState exitState)) = true ∨
          C17KNext? exitState = none)
      (inputA : C17Lemma1aInputA)
      (hrow : inputA.row =
        c17KFirstHitGlobalEntryRow (c17KBreakState exitState)) :
      C17Lemma1aReachabilityCover q
theorem c17_kexit_witness_to_inputA
    {seed : C17KState} {step : Nat}
    (hexit : C17KExitsDetectorAt seed step) :
    ∃ exitState : C17KState,
    ∃ inputA : C17Lemma1aInputA,
      C17KIter? seed step = some exitState ∧
        (c17L1ClassIsExit (c17L1Class (c17KBreakState exitState)) = true ∨
          C17KNext? exitState = none) ∧
        inputA.row = c17KFirstHitGlobalEntryRow (c17KBreakState exitState) := by
  obtain ⟨exitState, row, hiter, hexitStop, _hmem, hbucket, hrow⟩ :=
    c17_kexit_witness_to_global_entry_row hexit
  exact ⟨exitState, { row := row, classified := hbucket }, hiter, hexitStop, hrow⟩
theorem c17_initial_odd_reachability_cover_to_inputA
    {q : Nat} {seed : C17KState}
    (hodd : Odd q)
    (hseed : c17InitialKState? q = some seed) :
    C17Lemma1aReachabilityCover q := by
  obtain ⟨step, hexitStep⟩ :=
    c17_reachable_korbit_exits_detector
      (c17_initial_kstate_following_of_odd hodd hseed)
  obtain ⟨exitState, inputA, hiter, hexitStop, hrow⟩ :=
    c17_kexit_witness_to_inputA hexitStep
  exact C17Lemma1aReachabilityCover.detectorExit
    hseed hiter hexitStop inputA hrow
theorem c17_reachability_cover_to_inputA
    {q : Nat}
    (cover : C17Lemma1aReachabilityCover q) :
    Nonempty C17Lemma1aInputA := by
  cases cover with
  | detectorExit hseed hiter hexitStop inputA hrow =>
      exact ⟨inputA⟩
structure C17AppendixDSuffixPullbackModuleClosed where
  downstreamRow :
    C17Lemma1aDownstreamCarrierRow
      C17Lemma1aGlobalEntryRow.cNext13Mod16ReentryBank
  auditBoundary : C15AuditBoundaryForResidualMenu
  finiteSplice :
    ∀ L, 1 <= L -> C15FiniteResidueFamilySpliceReduction L
  residualMenu : C15ExhaustiveFiniteResidualMenu
  residualRowsLand :
    C15AuditedResidualMenuLandsInDirectDescent
  baseTemplateBoundary :
    ∀ u, C15AcceptedBaseTemplateBoundary (c15AcceptedBaseTemplateQ u)
  boundedStock : C17FixedStockBoundedKernelEvidence
  terminalStockClosed : C17RecordedTerminalDownstreamStockLedgerClosed
noncomputable def c17_appendixD_suffix_pullback_module_closed :
    C17AppendixDSuffixPullbackModuleClosed :=
  { downstreamRow := by rfl
    auditBoundary := c15_audit_boundary_for_residual_menu
    finiteSplice := c15_finite_residue_family_splice_reduction
    residualMenu := c15_exhaustive_finite_residual_menu
    residualRowsLand := c15_audited_residual_menu_lands_in_direct_descent
    baseTemplateBoundary := c15_accepted_base_template_boundary
    boundedStock := c17_fixed_stock_bounded_kernel_evidence
    terminalStockClosed := c17_lemma1a_recorded_terminal_downstream_stock_closed }
