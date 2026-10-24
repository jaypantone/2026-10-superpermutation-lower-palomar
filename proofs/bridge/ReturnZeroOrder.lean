module

public import bridge.ReturnZeroMap

@[expose] public section

/-! The seven-anchor cycle calculation, uniform in n. All finite cases are
on the residue modulo seven, never on the factorial-sized permutation graph. -/
namespace SuperpermutationBounds.ChainReturns
open Equiv

private theorem power_step {α : Type*} (f : Perm α) {p q : ℕ} {a b c : α}
    (hp : (f^p) a = b) (hq : (f^q) b = c) : (f^(p+q)) a = c := by
  rw [Nat.add_comm p q, pow_add, Perm.mul_apply, hp, hq]

private theorem fixed_before_power {α : Type*} (f : Perm α) {q R : ℕ} {a b : α}
    (hq : (f^q) a = b) (hR : (f^R) b = b) : (f^R) a = a := by
  apply (f^q).injective
  calc
    (f^q) ((f^R) a) = (f^R) ((f^q) a) := by
      rw [← Perm.mul_apply, ← Perm.mul_apply, ← pow_add, ← pow_add, Nat.add_comm]
    _ = (f^q) a := by rw [hq, hR]

/-- It suffices to check the seven bottom coordinates. -/
theorem zeroMap_eq_one_of_anchors {n : ℕ} (hn : 9 ≤ n) (R : ℕ)
    (H : ∀ a : ℕ, ∀ ha : a < 7,
      (zeroMap n (by omega)^R) ⟨a, by omega⟩ = ⟨a, by omega⟩) :
    zeroMap n (by omega)^R = 1 := by
  apply Equiv.ext
  intro x
  change (zeroMap n (by omega)^R) x = x
  by_cases hx : x.val < 7
  · exact H x.val hx
  · let q := x.val / 7
    let r := x.val % 7
    have hq : 0 < q := by dsimp [q]; omega
    have hr : r < 7 := Nat.mod_lt _ (by omega)
    have hd : x.val = 7*q+r := by dsimp [q,r]; omega
    have hh := zeroMap_descent_pow hn q hq r hr x hd
    apply fixed_before_power (zeroMap n (by omega)) hh
    let y := zeroSwap n (by omega) (⟨r, by omega⟩ : Fin n)
    have hy : y.val < 7 := by
      dsimp [y]
      rw [zeroSwap_val]
      change (if r = 0 then 1 else if r = 1 then 0 else r) < 7
      split_ifs <;> omega
    exact H y.val hy

/-- The product of the weighted anchor-cycle lengths. -/
def zeroExponent (n : ℕ) : ℕ :=
  let d := n / 7
  match n % 7 with
  | 0 => 2*d
  | 1 => d*(6*d+1)
  | 2 => (4*d+1)*(3*d+1)
  | 3 => (5*d+2)*(2*d+1)
  | 4 => (2*d+1)*(5*d+3)
  | 5 => (3*d+2)*(4*d+3)
  | _ => (6*d+5)*(d+1)

theorem zeroExponent_eq_returnZero {n : ℕ} (hn : 9 ≤ n) : zeroExponent n = returnZero n := by
  have hres : n % 7 < 7 := Nat.mod_lt _ (by omega)
  interval_cases hr : n % 7
  · simp only [zeroExponent, returnZero, hr, ite_true]
    omega
  · have hu : inverseSeven n = (6 * (n / 7) + 1) := by
      apply inverseSeven_eq_of_spec (by omega) (by omega) (by omega)
      have he : 7 * (6 * (n / 7) + 1) = 6 * n + 1 := by omega
      rw [he]
      simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < n)]
    simp only [zeroExponent, returnZero, hr, show (1:ℕ) ≠ 0 by omega, ite_false, hu]
    have hd : n - (6 * (n / 7) + 1) = 1 * (n / 7) + 0 := by omega
    rw [hd]
    ring
  · have hu : inverseSeven n = (3 * (n / 7) + 1) := by
      apply inverseSeven_eq_of_spec (by omega) (by omega) (by omega)
      have he : 7 * (3 * (n / 7) + 1) = 3 * n + 1 := by omega
      rw [he]
      simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < n)]
    simp only [zeroExponent, returnZero, hr, show (2:ℕ) ≠ 0 by omega, ite_false, hu]
    have hd : n - (3 * (n / 7) + 1) = 4 * (n / 7) + 1 := by omega
    rw [hd]
    ring
  · have hu : inverseSeven n = (2 * (n / 7) + 1) := by
      apply inverseSeven_eq_of_spec (by omega) (by omega) (by omega)
      have he : 7 * (2 * (n / 7) + 1) = 2 * n + 1 := by omega
      rw [he]
      simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < n)]
    simp only [zeroExponent, returnZero, hr, show (3:ℕ) ≠ 0 by omega, ite_false, hu]
    have hd : n - (2 * (n / 7) + 1) = 5 * (n / 7) + 2 := by omega
    rw [hd]
    ring
  · have hu : inverseSeven n = (5 * (n / 7) + 3) := by
      apply inverseSeven_eq_of_spec (by omega) (by omega) (by omega)
      have he : 7 * (5 * (n / 7) + 3) = 5 * n + 1 := by omega
      rw [he]
      simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < n)]
    simp only [zeroExponent, returnZero, hr, show (4:ℕ) ≠ 0 by omega, ite_false, hu]
    have hd : n - (5 * (n / 7) + 3) = 2 * (n / 7) + 1 := by omega
    rw [hd]
    ring
  · have hu : inverseSeven n = (4 * (n / 7) + 3) := by
      apply inverseSeven_eq_of_spec (by omega) (by omega) (by omega)
      have he : 7 * (4 * (n / 7) + 3) = 4 * n + 1 := by omega
      rw [he]
      simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < n)]
    simp only [zeroExponent, returnZero, hr, show (5:ℕ) ≠ 0 by omega, ite_false, hu]
    have hd : n - (4 * (n / 7) + 3) = 3 * (n / 7) + 2 := by omega
    rw [hd]
    ring
  · have hu : inverseSeven n = (1 * (n / 7) + 1) := by
      apply inverseSeven_eq_of_spec (by omega) (by omega) (by omega)
      have he : 7 * (1 * (n / 7) + 1) = 1 * n + 1 := by omega
      rw [he]
      simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
    simp only [zeroExponent, returnZero, hr, show (6:ℕ) ≠ 0 by omega, ite_false, hu]
    have hd : n - (1 * (n / 7) + 1) = 6 * (n / 7) + 5 := by omega
    rw [hd]
    ring


private theorem zeroSwap_mk {n : ℕ} (hn : 2 ≤ n) (a : ℕ) (ha : a < n) :
    zeroSwap n hn ⟨a, ha⟩ =
      ⟨if a = 0 then 1 else if a = 1 then 0 else a, by split_ifs <;> omega⟩ := by
  apply Fin.ext
  simpa only [Fin.val_mk] using zeroSwap_val hn (⟨a, ha⟩ : Fin n)

/-- The exact return exponent of the canonical alternating map. This uses
only seven residue cases, with their return clocks symbolic in n/7. -/
theorem zeroMap_return {n : ℕ} (hn : 9 ≤ n) :
    zeroMap n (by omega)^returnZero n = 1 := by
  rw [← zeroExponent_eq_returnZero hn]
  apply zeroMap_eq_one_of_anchors hn
  intro a ha
  let d := n / 7
  let f := zeroMap n (by omega : 2 ≤ n)
  have hres : n % 7 < 7 := Nat.mod_lt _ (by omega)
  interval_cases hr : n % 7
  · simp only [zeroExponent, hr]
    change (f^(2*d)) ⟨a, by omega⟩ = ⟨a, by omega⟩
    have h0 : (f^(d+0)) ⟨0, by omega⟩ = ⟨1, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 0 (by omega)
      have ht : (n + 0) / 7 = d+0 := rfl
      have hm : (n + 0) % 7 = 0 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h1 : (f^(d+0)) ⟨1, by omega⟩ = ⟨0, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 1 (by omega)
      have ht : (n + 1) / 7 = d+0 := by dsimp [d]; omega
      have hm : (n + 1) % 7 = 1 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h2 : (f^(d+0)) ⟨2, by omega⟩ = ⟨2, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 2 (by omega)
      have ht : (n + 2) / 7 = d+0 := by dsimp [d]; omega
      have hm : (n + 2) % 7 = 2 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h3 : (f^(d+0)) ⟨3, by omega⟩ = ⟨3, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 3 (by omega)
      have ht : (n + 3) / 7 = d+0 := by dsimp [d]; omega
      have hm : (n + 3) % 7 = 3 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h4 : (f^(d+0)) ⟨4, by omega⟩ = ⟨4, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 4 (by omega)
      have ht : (n + 4) / 7 = d+0 := by dsimp [d]; omega
      have hm : (n + 4) % 7 = 4 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h5 : (f^(d+0)) ⟨5, by omega⟩ = ⟨5, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 5 (by omega)
      have ht : (n + 5) / 7 = d+0 := by dsimp [d]; omega
      have hm : (n + 5) % 7 = 5 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h6 : (f^(d+0)) ⟨6, by omega⟩ = ⟨6, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 6 (by omega)
      have ht : (n + 6) / 7 = d+0 := by dsimp [d]; omega
      have hm : (n + 6) % 7 = 6 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    interval_cases a
    · have hc := (power_step f h0 h1)
      have he : ((d+0) + (d+0)) = (2*d+0) := by omega
      rw [he] at hc
      rw [show 2*d = (2*d+0) * 1 by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc 1
    · have hc := (power_step f h1 h0)
      have he : ((d+0) + (d+0)) = (2*d+0) := by omega
      rw [he] at hc
      rw [show 2*d = (2*d+0) * 1 by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc 1
    · have hc := h2
      have he : (d+0) = (1*d+0) := by omega
      rw [he] at hc
      rw [show 2*d = (1*d+0) * 2 by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc 2
    · have hc := h3
      have he : (d+0) = (1*d+0) := by omega
      rw [he] at hc
      rw [show 2*d = (1*d+0) * 2 by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc 2
    · have hc := h4
      have he : (d+0) = (1*d+0) := by omega
      rw [he] at hc
      rw [show 2*d = (1*d+0) * 2 by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc 2
    · have hc := h5
      have he : (d+0) = (1*d+0) := by omega
      rw [he] at hc
      rw [show 2*d = (1*d+0) * 2 by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc 2
    · have hc := h6
      have he : (d+0) = (1*d+0) := by omega
      rw [he] at hc
      rw [show 2*d = (1*d+0) * 2 by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc 2
  · simp only [zeroExponent, hr]
    change (f^(d*(6*d+1))) ⟨a, by omega⟩ = ⟨a, by omega⟩
    have h0 : (f^(d+0)) ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 0 (by omega)
      have ht : (n + 0) / 7 = d+0 := rfl
      have hm : (n + 0) % 7 = 1 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h1 : (f^(d+0)) ⟨1, by omega⟩ = ⟨2, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 1 (by omega)
      have ht : (n + 1) / 7 = d+0 := by dsimp [d]; omega
      have hm : (n + 1) % 7 = 2 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h2 : (f^(d+0)) ⟨2, by omega⟩ = ⟨3, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 2 (by omega)
      have ht : (n + 2) / 7 = d+0 := by dsimp [d]; omega
      have hm : (n + 2) % 7 = 3 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h3 : (f^(d+0)) ⟨3, by omega⟩ = ⟨4, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 3 (by omega)
      have ht : (n + 3) / 7 = d+0 := by dsimp [d]; omega
      have hm : (n + 3) % 7 = 4 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h4 : (f^(d+0)) ⟨4, by omega⟩ = ⟨5, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 4 (by omega)
      have ht : (n + 4) / 7 = d+0 := by dsimp [d]; omega
      have hm : (n + 4) % 7 = 5 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h5 : (f^(d+0)) ⟨5, by omega⟩ = ⟨6, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 5 (by omega)
      have ht : (n + 5) / 7 = d+0 := by dsimp [d]; omega
      have hm : (n + 5) % 7 = 6 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h6 : (f^(d+1)) ⟨6, by omega⟩ = ⟨1, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 6 (by omega)
      have ht : (n + 6) / 7 = d+1 := by dsimp [d]; omega
      have hm : (n + 6) % 7 = 0 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    interval_cases a
    · have hc := h0
      have he : (d+0) = (1*d+0) := by omega
      rw [he] at hc
      rw [show d*(6*d+1) = (1*d+0) * (6*d+1) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (6*d+1)
    · have hc := (power_step f (power_step f (power_step f (power_step f (power_step f h1 h2) h3) h4) h5) h6)
      have he : ((((((d+0) + (d+0)) + (d+0)) + (d+0)) + (d+0)) + (d+1)) = (6*d+1) := by omega
      rw [he] at hc
      rw [show d*(6*d+1) = (6*d+1) * (1*d+0) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (1*d+0)
    · have hc := (power_step f (power_step f (power_step f (power_step f (power_step f h2 h3) h4) h5) h6) h1)
      have he : ((((((d+0) + (d+0)) + (d+0)) + (d+0)) + (d+1)) + (d+0)) = (6*d+1) := by omega
      rw [he] at hc
      rw [show d*(6*d+1) = (6*d+1) * (1*d+0) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (1*d+0)
    · have hc := (power_step f (power_step f (power_step f (power_step f (power_step f h3 h4) h5) h6) h1) h2)
      have he : ((((((d+0) + (d+0)) + (d+0)) + (d+1)) + (d+0)) + (d+0)) = (6*d+1) := by omega
      rw [he] at hc
      rw [show d*(6*d+1) = (6*d+1) * (1*d+0) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (1*d+0)
    · have hc := (power_step f (power_step f (power_step f (power_step f (power_step f h4 h5) h6) h1) h2) h3)
      have he : ((((((d+0) + (d+0)) + (d+1)) + (d+0)) + (d+0)) + (d+0)) = (6*d+1) := by omega
      rw [he] at hc
      rw [show d*(6*d+1) = (6*d+1) * (1*d+0) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (1*d+0)
    · have hc := (power_step f (power_step f (power_step f (power_step f (power_step f h5 h6) h1) h2) h3) h4)
      have he : ((((((d+0) + (d+1)) + (d+0)) + (d+0)) + (d+0)) + (d+0)) = (6*d+1) := by omega
      rw [he] at hc
      rw [show d*(6*d+1) = (6*d+1) * (1*d+0) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (1*d+0)
    · have hc := (power_step f (power_step f (power_step f (power_step f (power_step f h6 h1) h2) h3) h4) h5)
      have he : ((((((d+1) + (d+0)) + (d+0)) + (d+0)) + (d+0)) + (d+0)) = (6*d+1) := by omega
      rw [he] at hc
      rw [show d*(6*d+1) = (6*d+1) * (1*d+0) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (1*d+0)
  · simp only [zeroExponent, hr]
    change (f^((4*d+1)*(3*d+1))) ⟨a, by omega⟩ = ⟨a, by omega⟩
    have h0 : (f^(d+0)) ⟨0, by omega⟩ = ⟨2, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 0 (by omega)
      have ht : (n + 0) / 7 = d+0 := rfl
      have hm : (n + 0) % 7 = 2 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h1 : (f^(d+0)) ⟨1, by omega⟩ = ⟨3, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 1 (by omega)
      have ht : (n + 1) / 7 = d+0 := by dsimp [d]; omega
      have hm : (n + 1) % 7 = 3 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h2 : (f^(d+0)) ⟨2, by omega⟩ = ⟨4, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 2 (by omega)
      have ht : (n + 2) / 7 = d+0 := by dsimp [d]; omega
      have hm : (n + 2) % 7 = 4 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h3 : (f^(d+0)) ⟨3, by omega⟩ = ⟨5, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 3 (by omega)
      have ht : (n + 3) / 7 = d+0 := by dsimp [d]; omega
      have hm : (n + 3) % 7 = 5 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h4 : (f^(d+0)) ⟨4, by omega⟩ = ⟨6, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 4 (by omega)
      have ht : (n + 4) / 7 = d+0 := by dsimp [d]; omega
      have hm : (n + 4) % 7 = 6 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h5 : (f^(d+1)) ⟨5, by omega⟩ = ⟨1, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 5 (by omega)
      have ht : (n + 5) / 7 = d+1 := by dsimp [d]; omega
      have hm : (n + 5) % 7 = 0 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h6 : (f^(d+1)) ⟨6, by omega⟩ = ⟨0, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 6 (by omega)
      have ht : (n + 6) / 7 = d+1 := by dsimp [d]; omega
      have hm : (n + 6) % 7 = 1 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    interval_cases a
    · have hc := (power_step f (power_step f (power_step f h0 h2) h4) h6)
      have he : ((((d+0) + (d+0)) + (d+0)) + (d+1)) = (4*d+1) := by omega
      rw [he] at hc
      rw [show (4*d+1)*(3*d+1) = (4*d+1) * (3*d+1) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (3*d+1)
    · have hc := (power_step f (power_step f h1 h3) h5)
      have he : (((d+0) + (d+0)) + (d+1)) = (3*d+1) := by omega
      rw [he] at hc
      rw [show (4*d+1)*(3*d+1) = (3*d+1) * (4*d+1) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (4*d+1)
    · have hc := (power_step f (power_step f (power_step f h2 h4) h6) h0)
      have he : ((((d+0) + (d+0)) + (d+1)) + (d+0)) = (4*d+1) := by omega
      rw [he] at hc
      rw [show (4*d+1)*(3*d+1) = (4*d+1) * (3*d+1) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (3*d+1)
    · have hc := (power_step f (power_step f h3 h5) h1)
      have he : (((d+0) + (d+1)) + (d+0)) = (3*d+1) := by omega
      rw [he] at hc
      rw [show (4*d+1)*(3*d+1) = (3*d+1) * (4*d+1) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (4*d+1)
    · have hc := (power_step f (power_step f (power_step f h4 h6) h0) h2)
      have he : ((((d+0) + (d+1)) + (d+0)) + (d+0)) = (4*d+1) := by omega
      rw [he] at hc
      rw [show (4*d+1)*(3*d+1) = (4*d+1) * (3*d+1) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (3*d+1)
    · have hc := (power_step f (power_step f h5 h1) h3)
      have he : (((d+1) + (d+0)) + (d+0)) = (3*d+1) := by omega
      rw [he] at hc
      rw [show (4*d+1)*(3*d+1) = (3*d+1) * (4*d+1) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (4*d+1)
    · have hc := (power_step f (power_step f (power_step f h6 h0) h2) h4)
      have he : ((((d+1) + (d+0)) + (d+0)) + (d+0)) = (4*d+1) := by omega
      rw [he] at hc
      rw [show (4*d+1)*(3*d+1) = (4*d+1) * (3*d+1) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (3*d+1)
  · simp only [zeroExponent, hr]
    change (f^((5*d+2)*(2*d+1))) ⟨a, by omega⟩ = ⟨a, by omega⟩
    have h0 : (f^(d+0)) ⟨0, by omega⟩ = ⟨3, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 0 (by omega)
      have ht : (n + 0) / 7 = d+0 := rfl
      have hm : (n + 0) % 7 = 3 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h1 : (f^(d+0)) ⟨1, by omega⟩ = ⟨4, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 1 (by omega)
      have ht : (n + 1) / 7 = d+0 := by dsimp [d]; omega
      have hm : (n + 1) % 7 = 4 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h2 : (f^(d+0)) ⟨2, by omega⟩ = ⟨5, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 2 (by omega)
      have ht : (n + 2) / 7 = d+0 := by dsimp [d]; omega
      have hm : (n + 2) % 7 = 5 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h3 : (f^(d+0)) ⟨3, by omega⟩ = ⟨6, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 3 (by omega)
      have ht : (n + 3) / 7 = d+0 := by dsimp [d]; omega
      have hm : (n + 3) % 7 = 6 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h4 : (f^(d+1)) ⟨4, by omega⟩ = ⟨1, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 4 (by omega)
      have ht : (n + 4) / 7 = d+1 := by dsimp [d]; omega
      have hm : (n + 4) % 7 = 0 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h5 : (f^(d+1)) ⟨5, by omega⟩ = ⟨0, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 5 (by omega)
      have ht : (n + 5) / 7 = d+1 := by dsimp [d]; omega
      have hm : (n + 5) % 7 = 1 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h6 : (f^(d+1)) ⟨6, by omega⟩ = ⟨2, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 6 (by omega)
      have ht : (n + 6) / 7 = d+1 := by dsimp [d]; omega
      have hm : (n + 6) % 7 = 2 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    interval_cases a
    · have hc := (power_step f (power_step f (power_step f (power_step f h0 h3) h6) h2) h5)
      have he : (((((d+0) + (d+0)) + (d+1)) + (d+0)) + (d+1)) = (5*d+2) := by omega
      rw [he] at hc
      rw [show (5*d+2)*(2*d+1) = (5*d+2) * (2*d+1) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (2*d+1)
    · have hc := (power_step f h1 h4)
      have he : ((d+0) + (d+1)) = (2*d+1) := by omega
      rw [he] at hc
      rw [show (5*d+2)*(2*d+1) = (2*d+1) * (5*d+2) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (5*d+2)
    · have hc := (power_step f (power_step f (power_step f (power_step f h2 h5) h0) h3) h6)
      have he : (((((d+0) + (d+1)) + (d+0)) + (d+0)) + (d+1)) = (5*d+2) := by omega
      rw [he] at hc
      rw [show (5*d+2)*(2*d+1) = (5*d+2) * (2*d+1) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (2*d+1)
    · have hc := (power_step f (power_step f (power_step f (power_step f h3 h6) h2) h5) h0)
      have he : (((((d+0) + (d+1)) + (d+0)) + (d+1)) + (d+0)) = (5*d+2) := by omega
      rw [he] at hc
      rw [show (5*d+2)*(2*d+1) = (5*d+2) * (2*d+1) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (2*d+1)
    · have hc := (power_step f h4 h1)
      have he : ((d+1) + (d+0)) = (2*d+1) := by omega
      rw [he] at hc
      rw [show (5*d+2)*(2*d+1) = (2*d+1) * (5*d+2) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (5*d+2)
    · have hc := (power_step f (power_step f (power_step f (power_step f h5 h0) h3) h6) h2)
      have he : (((((d+1) + (d+0)) + (d+0)) + (d+1)) + (d+0)) = (5*d+2) := by omega
      rw [he] at hc
      rw [show (5*d+2)*(2*d+1) = (5*d+2) * (2*d+1) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (2*d+1)
    · have hc := (power_step f (power_step f (power_step f (power_step f h6 h2) h5) h0) h3)
      have he : (((((d+1) + (d+0)) + (d+1)) + (d+0)) + (d+0)) = (5*d+2) := by omega
      rw [he] at hc
      rw [show (5*d+2)*(2*d+1) = (5*d+2) * (2*d+1) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (2*d+1)
  · simp only [zeroExponent, hr]
    change (f^((2*d+1)*(5*d+3))) ⟨a, by omega⟩ = ⟨a, by omega⟩
    have h0 : (f^(d+0)) ⟨0, by omega⟩ = ⟨4, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 0 (by omega)
      have ht : (n + 0) / 7 = d+0 := rfl
      have hm : (n + 0) % 7 = 4 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h1 : (f^(d+0)) ⟨1, by omega⟩ = ⟨5, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 1 (by omega)
      have ht : (n + 1) / 7 = d+0 := by dsimp [d]; omega
      have hm : (n + 1) % 7 = 5 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h2 : (f^(d+0)) ⟨2, by omega⟩ = ⟨6, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 2 (by omega)
      have ht : (n + 2) / 7 = d+0 := by dsimp [d]; omega
      have hm : (n + 2) % 7 = 6 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h3 : (f^(d+1)) ⟨3, by omega⟩ = ⟨1, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 3 (by omega)
      have ht : (n + 3) / 7 = d+1 := by dsimp [d]; omega
      have hm : (n + 3) % 7 = 0 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h4 : (f^(d+1)) ⟨4, by omega⟩ = ⟨0, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 4 (by omega)
      have ht : (n + 4) / 7 = d+1 := by dsimp [d]; omega
      have hm : (n + 4) % 7 = 1 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h5 : (f^(d+1)) ⟨5, by omega⟩ = ⟨2, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 5 (by omega)
      have ht : (n + 5) / 7 = d+1 := by dsimp [d]; omega
      have hm : (n + 5) % 7 = 2 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h6 : (f^(d+1)) ⟨6, by omega⟩ = ⟨3, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 6 (by omega)
      have ht : (n + 6) / 7 = d+1 := by dsimp [d]; omega
      have hm : (n + 6) % 7 = 3 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    interval_cases a
    · have hc := (power_step f h0 h4)
      have he : ((d+0) + (d+1)) = (2*d+1) := by omega
      rw [he] at hc
      rw [show (2*d+1)*(5*d+3) = (2*d+1) * (5*d+3) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (5*d+3)
    · have hc := (power_step f (power_step f (power_step f (power_step f h1 h5) h2) h6) h3)
      have he : (((((d+0) + (d+1)) + (d+0)) + (d+1)) + (d+1)) = (5*d+3) := by omega
      rw [he] at hc
      rw [show (2*d+1)*(5*d+3) = (5*d+3) * (2*d+1) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (2*d+1)
    · have hc := (power_step f (power_step f (power_step f (power_step f h2 h6) h3) h1) h5)
      have he : (((((d+0) + (d+1)) + (d+1)) + (d+0)) + (d+1)) = (5*d+3) := by omega
      rw [he] at hc
      rw [show (2*d+1)*(5*d+3) = (5*d+3) * (2*d+1) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (2*d+1)
    · have hc := (power_step f (power_step f (power_step f (power_step f h3 h1) h5) h2) h6)
      have he : (((((d+1) + (d+0)) + (d+1)) + (d+0)) + (d+1)) = (5*d+3) := by omega
      rw [he] at hc
      rw [show (2*d+1)*(5*d+3) = (5*d+3) * (2*d+1) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (2*d+1)
    · have hc := (power_step f h4 h0)
      have he : ((d+1) + (d+0)) = (2*d+1) := by omega
      rw [he] at hc
      rw [show (2*d+1)*(5*d+3) = (2*d+1) * (5*d+3) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (5*d+3)
    · have hc := (power_step f (power_step f (power_step f (power_step f h5 h2) h6) h3) h1)
      have he : (((((d+1) + (d+0)) + (d+1)) + (d+1)) + (d+0)) = (5*d+3) := by omega
      rw [he] at hc
      rw [show (2*d+1)*(5*d+3) = (5*d+3) * (2*d+1) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (2*d+1)
    · have hc := (power_step f (power_step f (power_step f (power_step f h6 h3) h1) h5) h2)
      have he : (((((d+1) + (d+1)) + (d+0)) + (d+1)) + (d+0)) = (5*d+3) := by omega
      rw [he] at hc
      rw [show (2*d+1)*(5*d+3) = (5*d+3) * (2*d+1) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (2*d+1)
  · simp only [zeroExponent, hr]
    change (f^((3*d+2)*(4*d+3))) ⟨a, by omega⟩ = ⟨a, by omega⟩
    have h0 : (f^(d+0)) ⟨0, by omega⟩ = ⟨5, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 0 (by omega)
      have ht : (n + 0) / 7 = d+0 := rfl
      have hm : (n + 0) % 7 = 5 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h1 : (f^(d+0)) ⟨1, by omega⟩ = ⟨6, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 1 (by omega)
      have ht : (n + 1) / 7 = d+0 := by dsimp [d]; omega
      have hm : (n + 1) % 7 = 6 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h2 : (f^(d+1)) ⟨2, by omega⟩ = ⟨1, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 2 (by omega)
      have ht : (n + 2) / 7 = d+1 := by dsimp [d]; omega
      have hm : (n + 2) % 7 = 0 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h3 : (f^(d+1)) ⟨3, by omega⟩ = ⟨0, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 3 (by omega)
      have ht : (n + 3) / 7 = d+1 := by dsimp [d]; omega
      have hm : (n + 3) % 7 = 1 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h4 : (f^(d+1)) ⟨4, by omega⟩ = ⟨2, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 4 (by omega)
      have ht : (n + 4) / 7 = d+1 := by dsimp [d]; omega
      have hm : (n + 4) % 7 = 2 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h5 : (f^(d+1)) ⟨5, by omega⟩ = ⟨3, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 5 (by omega)
      have ht : (n + 5) / 7 = d+1 := by dsimp [d]; omega
      have hm : (n + 5) % 7 = 3 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h6 : (f^(d+1)) ⟨6, by omega⟩ = ⟨4, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 6 (by omega)
      have ht : (n + 6) / 7 = d+1 := by dsimp [d]; omega
      have hm : (n + 6) % 7 = 4 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    interval_cases a
    · have hc := (power_step f (power_step f h0 h5) h3)
      have he : (((d+0) + (d+1)) + (d+1)) = (3*d+2) := by omega
      rw [he] at hc
      rw [show (3*d+2)*(4*d+3) = (3*d+2) * (4*d+3) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (4*d+3)
    · have hc := (power_step f (power_step f (power_step f h1 h6) h4) h2)
      have he : ((((d+0) + (d+1)) + (d+1)) + (d+1)) = (4*d+3) := by omega
      rw [he] at hc
      rw [show (3*d+2)*(4*d+3) = (4*d+3) * (3*d+2) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (3*d+2)
    · have hc := (power_step f (power_step f (power_step f h2 h1) h6) h4)
      have he : ((((d+1) + (d+0)) + (d+1)) + (d+1)) = (4*d+3) := by omega
      rw [he] at hc
      rw [show (3*d+2)*(4*d+3) = (4*d+3) * (3*d+2) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (3*d+2)
    · have hc := (power_step f (power_step f h3 h0) h5)
      have he : (((d+1) + (d+0)) + (d+1)) = (3*d+2) := by omega
      rw [he] at hc
      rw [show (3*d+2)*(4*d+3) = (3*d+2) * (4*d+3) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (4*d+3)
    · have hc := (power_step f (power_step f (power_step f h4 h2) h1) h6)
      have he : ((((d+1) + (d+1)) + (d+0)) + (d+1)) = (4*d+3) := by omega
      rw [he] at hc
      rw [show (3*d+2)*(4*d+3) = (4*d+3) * (3*d+2) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (3*d+2)
    · have hc := (power_step f (power_step f h5 h3) h0)
      have he : (((d+1) + (d+1)) + (d+0)) = (3*d+2) := by omega
      rw [he] at hc
      rw [show (3*d+2)*(4*d+3) = (3*d+2) * (4*d+3) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (4*d+3)
    · have hc := (power_step f (power_step f (power_step f h6 h4) h2) h1)
      have he : ((((d+1) + (d+1)) + (d+1)) + (d+0)) = (4*d+3) := by omega
      rw [he] at hc
      rw [show (3*d+2)*(4*d+3) = (4*d+3) * (3*d+2) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (3*d+2)
  · simp only [zeroExponent, hr]
    change (f^((6*d+5)*(d+1))) ⟨a, by omega⟩ = ⟨a, by omega⟩
    have h0 : (f^(d+0)) ⟨0, by omega⟩ = ⟨6, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 0 (by omega)
      have ht : (n + 0) / 7 = d+0 := rfl
      have hm : (n + 0) % 7 = 6 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h1 : (f^(d+1)) ⟨1, by omega⟩ = ⟨1, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 1 (by omega)
      have ht : (n + 1) / 7 = d+1 := by dsimp [d]; omega
      have hm : (n + 1) % 7 = 0 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h2 : (f^(d+1)) ⟨2, by omega⟩ = ⟨0, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 2 (by omega)
      have ht : (n + 2) / 7 = d+1 := by dsimp [d]; omega
      have hm : (n + 2) % 7 = 1 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h3 : (f^(d+1)) ⟨3, by omega⟩ = ⟨2, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 3 (by omega)
      have ht : (n + 3) / 7 = d+1 := by dsimp [d]; omega
      have hm : (n + 3) % 7 = 2 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h4 : (f^(d+1)) ⟨4, by omega⟩ = ⟨3, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 4 (by omega)
      have ht : (n + 4) / 7 = d+1 := by dsimp [d]; omega
      have hm : (n + 4) % 7 = 3 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h5 : (f^(d+1)) ⟨5, by omega⟩ = ⟨4, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 5 (by omega)
      have ht : (n + 5) / 7 = d+1 := by dsimp [d]; omega
      have hm : (n + 5) % 7 = 4 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    have h6 : (f^(d+1)) ⟨6, by omega⟩ = ⟨5, by omega⟩ := by
      have hh := zeroMap_anchor_return hn 6 (by omega)
      have ht : (n + 6) / 7 = d+1 := by dsimp [d]; omega
      have hm : (n + 6) % 7 = 5 := by omega
      rw [ht] at hh
      have hv := congrArg Fin.val hh
      rw [zeroSwap_val] at hv
      norm_num [hm, hr] at hv
      exact Fin.ext hv
    interval_cases a
    · have hc := (power_step f (power_step f (power_step f (power_step f (power_step f h0 h6) h5) h4) h3) h2)
      have he : ((((((d+0) + (d+1)) + (d+1)) + (d+1)) + (d+1)) + (d+1)) = (6*d+5) := by omega
      rw [he] at hc
      rw [show (6*d+5)*(d+1) = (6*d+5) * (1*d+1) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (1*d+1)
    · have hc := h1
      have he : (d+1) = (1*d+1) := by omega
      rw [he] at hc
      rw [show (6*d+5)*(d+1) = (1*d+1) * (6*d+5) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (6*d+5)
    · have hc := (power_step f (power_step f (power_step f (power_step f (power_step f h2 h0) h6) h5) h4) h3)
      have he : ((((((d+1) + (d+0)) + (d+1)) + (d+1)) + (d+1)) + (d+1)) = (6*d+5) := by omega
      rw [he] at hc
      rw [show (6*d+5)*(d+1) = (6*d+5) * (1*d+1) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (1*d+1)
    · have hc := (power_step f (power_step f (power_step f (power_step f (power_step f h3 h2) h0) h6) h5) h4)
      have he : ((((((d+1) + (d+1)) + (d+0)) + (d+1)) + (d+1)) + (d+1)) = (6*d+5) := by omega
      rw [he] at hc
      rw [show (6*d+5)*(d+1) = (6*d+5) * (1*d+1) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (1*d+1)
    · have hc := (power_step f (power_step f (power_step f (power_step f (power_step f h4 h3) h2) h0) h6) h5)
      have he : ((((((d+1) + (d+1)) + (d+1)) + (d+0)) + (d+1)) + (d+1)) = (6*d+5) := by omega
      rw [he] at hc
      rw [show (6*d+5)*(d+1) = (6*d+5) * (1*d+1) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (1*d+1)
    · have hc := (power_step f (power_step f (power_step f (power_step f (power_step f h5 h4) h3) h2) h0) h6)
      have he : ((((((d+1) + (d+1)) + (d+1)) + (d+1)) + (d+0)) + (d+1)) = (6*d+5) := by omega
      rw [he] at hc
      rw [show (6*d+5)*(d+1) = (6*d+5) * (1*d+1) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (1*d+1)
    · have hc := (power_step f (power_step f (power_step f (power_step f (power_step f h6 h5) h4) h3) h2) h0)
      have he : ((((((d+1) + (d+1)) + (d+1)) + (d+1)) + (d+1)) + (d+0)) = (6*d+5) := by omega
      rw [he] at hc
      rw [show (6*d+5)*(d+1) = (6*d+5) * (1*d+1) by ring, pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self hc (1*d+1)

end SuperpermutationBounds.ChainReturns
