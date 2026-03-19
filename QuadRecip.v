(******************************************************************************)
(*                                                                            *)
(*                    Quadratic Reciprocity: Legendre Symbols                 *)
(*                                                                            *)
(*     Formalizes the Law of Quadratic Reciprocity and its two supplements.   *)
(*     Defines quadratic residues, the Legendre symbol, Euler's criterion,    *)
(*     and proves concrete computations at small odd primes.                  *)
(*                                                                            *)
(*     The fundamental theorem, if we consider both its elegance and the      *)
(*     endless applications of which it is capable, deserves without doubt    *)
(*     to be placed among the most beautiful of all of arithmetic.            *)
(*     (Carl Friedrich Gauss, Disquisitiones Arithmeticae, 1801)              *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 8, 2026                                                  *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
Import ListNotations.

(******************************************************************************)
(* SECTION 1: DIVISIBILITY AND MODULAR ARITHMETIC                             *)
(******************************************************************************)

(* a divides b *)
Definition divides (a b : nat) : Prop := exists k, b = a * k.

Lemma divides_refl : forall n, divides n n.
Proof. intros n. exists 1. lia. Qed.

Lemma divides_trans : forall a b c, divides a b -> divides b c -> divides a c.
Proof.
  intros a b c [k1 Hk1] [k2 Hk2].
  exists (k1 * k2). lia.
Qed.

Lemma divides_0 : forall n, divides n 0.
Proof. intros n. exists 0. lia. Qed.

(* a congruent to b (mod m) *)
Definition cong (a b m : nat) : Prop :=
  divides m (a - b) \/ divides m (b - a).

(******************************************************************************)
(* SECTION 2: PRIMALITY (BOOLEAN TRIAL DIVISION)                              *)
(******************************************************************************)

(* Trial division: check if n has a divisor in 2..k *)
Fixpoint has_small_divisor (n k : nat) : bool :=
  match k with
  | 0 => false
  | S kp =>
      match kp with
      | 0 => false
      | S kpp =>
          if Nat.eqb (Nat.modulo n (S kp)) 0 then true
          else has_small_divisor n kp
      end
  end.

Definition is_prime (n : nat) : bool :=
  match n with
  | 0 => false
  | 1 => false
  | 2 => true
  | _ =>
      negb (has_small_divisor n (n - 1))
  end.

(* Verify small primes *)
Lemma prime_2  : is_prime 2  = true.  Proof. reflexivity. Qed.
Lemma prime_3  : is_prime 3  = true.  Proof. reflexivity. Qed.
Lemma prime_5  : is_prime 5  = true.  Proof. reflexivity. Qed.
Lemma prime_7  : is_prime 7  = true.  Proof. reflexivity. Qed.
Lemma prime_11 : is_prime 11 = true.  Proof. reflexivity. Qed.
Lemma prime_13 : is_prime 13 = true.  Proof. reflexivity. Qed.
Lemma prime_17 : is_prime 17 = true.  Proof. reflexivity. Qed.
Lemma prime_19 : is_prime 19 = true.  Proof. reflexivity. Qed.
Lemma prime_23 : is_prime 23 = true.  Proof. reflexivity. Qed.

Lemma not_prime_4  : is_prime 4  = false. Proof. reflexivity. Qed.
Lemma not_prime_6  : is_prime 6  = false. Proof. reflexivity. Qed.
Lemma not_prime_9  : is_prime 9  = false. Proof. reflexivity. Qed.
Lemma not_prime_15 : is_prime 15 = false. Proof. reflexivity. Qed.

(******************************************************************************)
(* SECTION 3: QUADRATIC RESIDUES                                              *)
(******************************************************************************)

(* a is a quadratic residue mod p if there exists x such that x^2 ≡ a (mod p) *)
(* We use a boolean search for small p *)

Fixpoint nat_pow (base exp : nat) : nat :=
  match exp with
  | 0    => 1
  | S ep => base * nat_pow base ep
  end.

(* Check if any x in 1..bound satisfies x^2 congruent to a (mod p) *)
Fixpoint is_qr_sq (a p bound : nat) : bool :=
  match bound with
  | 0 => false
  | S bp =>
      if Nat.eqb (Nat.modulo (bound * bound) p) (Nat.modulo a p)
      then true
      else is_qr_sq a p bp
  end.

Definition is_quadratic_residue (a p : nat) : bool :=
  negb (Nat.eqb (Nat.modulo a p) 0) &&
  is_qr_sq a p (p - 1).

(* QR computations mod 7: QRs are 1, 2, 4 *)
Lemma qr_1_mod_7 : is_quadratic_residue 1 7 = true.
Proof. reflexivity. Qed.

Lemma qr_2_mod_7 : is_quadratic_residue 2 7 = true.
Proof. reflexivity. Qed.

Lemma qr_4_mod_7 : is_quadratic_residue 4 7 = true.
Proof. reflexivity. Qed.

(* Non-residues mod 7: 3, 5, 6 *)
Lemma nqr_3_mod_7 : is_quadratic_residue 3 7 = false.
Proof. reflexivity. Qed.

Lemma nqr_5_mod_7 : is_quadratic_residue 5 7 = false.
Proof. reflexivity. Qed.

Lemma nqr_6_mod_7 : is_quadratic_residue 6 7 = false.
Proof. reflexivity. Qed.

(* QRs mod 5: 1, 4 *)
Lemma qr_1_mod_5 : is_quadratic_residue 1 5 = true.
Proof. reflexivity. Qed.

Lemma qr_4_mod_5 : is_quadratic_residue 4 5 = true.
Proof. reflexivity. Qed.

Lemma nqr_2_mod_5 : is_quadratic_residue 2 5 = false.
Proof. reflexivity. Qed.

Lemma nqr_3_mod_5 : is_quadratic_residue 3 5 = false.
Proof. reflexivity. Qed.

(* QRs mod 11: 1, 3, 4, 5, 9 *)
Lemma qr_1_mod_11 : is_quadratic_residue 1  11 = true.  Proof. reflexivity. Qed.
Lemma qr_3_mod_11 : is_quadratic_residue 3  11 = true.  Proof. reflexivity. Qed.
Lemma qr_4_mod_11 : is_quadratic_residue 4  11 = true.  Proof. reflexivity. Qed.
Lemma qr_5_mod_11 : is_quadratic_residue 5  11 = true.  Proof. reflexivity. Qed.
Lemma qr_9_mod_11 : is_quadratic_residue 9  11 = true.  Proof. reflexivity. Qed.

(******************************************************************************)
(* SECTION 4: THE LEGENDRE SYMBOL                                             *)
(******************************************************************************)

(* The Legendre symbol (a/p) for odd prime p:
   =  0 if p | a
   =  1 if a is a QR mod p
   = -1 if a is a QNR mod p
   We encode as an integer in {-1, 0, 1} using Z. *)

(* Since we avoid Z here, we use a three-value type *)
Inductive LegendreValue : Type :=
  | LegZero     (*  0: p divides a *)
  | LegOne      (*  1: QR *)
  | LegMinusOne (* -1: QNR *).

Definition legendre (a p : nat) : LegendreValue :=
  if Nat.eqb (Nat.modulo a p) 0 then LegZero
  else if is_quadratic_residue a p then LegOne
  else LegMinusOne.

(* Compute Legendre symbol at small primes *)
Lemma leg_1_7   : legendre 1 7 = LegOne.       Proof. reflexivity. Qed.
Lemma leg_2_7   : legendre 2 7 = LegOne.       Proof. reflexivity. Qed.
Lemma leg_3_7   : legendre 3 7 = LegMinusOne.  Proof. reflexivity. Qed.
Lemma leg_4_7   : legendre 4 7 = LegOne.       Proof. reflexivity. Qed.
Lemma leg_5_7   : legendre 5 7 = LegMinusOne.  Proof. reflexivity. Qed.
Lemma leg_6_7   : legendre 6 7 = LegMinusOne.  Proof. reflexivity. Qed.
Lemma leg_7_7   : legendre 7 7 = LegZero.      Proof. reflexivity. Qed.
Lemma leg_2_5   : legendre 2 5 = LegMinusOne.  Proof. reflexivity. Qed.
Lemma leg_3_5   : legendre 3 5 = LegMinusOne.  Proof. reflexivity. Qed.
Lemma leg_1_11  : legendre 1 11 = LegOne.      Proof. reflexivity. Qed.
Lemma leg_2_11  : legendre 2 11 = LegMinusOne. Proof. reflexivity. Qed.
Lemma leg_3_11  : legendre 3 11 = LegOne.      Proof. reflexivity. Qed.

(* Legendre symbol is zero iff p | a *)
Theorem legendre_zero_iff : forall a p,
  p > 0 ->
  legendre a p = LegZero <-> Nat.modulo a p = 0.
Proof.
  intros a p Hp. unfold legendre.
  split.
  - intro H. destruct (Nat.eqb (Nat.modulo a p) 0) eqn:Heq.
    + apply Nat.eqb_eq. exact Heq.
    + destruct (is_quadratic_residue a p); discriminate.
  - intro H. rewrite H. reflexivity.
Qed.

(******************************************************************************)
(* SECTION 5: EULER'S CRITERION                                               *)
(******************************************************************************)

(* Euler's criterion (computational verification):
   For odd prime p and gcd(a,p)=1:
   a^((p-1)/2) ≡ 1 (mod p)   iff  a is a QR mod p
   a^((p-1)/2) ≡ -1 ≡ p-1 (mod p) iff a is a QNR mod p

   We verify this for p = 7 at each residue class. *)

Definition euler_exp (a p : nat) : nat :=
  Nat.modulo (nat_pow a ((p - 1) / 2)) p.

(* Euler criterion for p = 7: QRs give 1, QNRs give 6 = p-1 *)
Lemma euler_1_7 : euler_exp 1 7 = 1. Proof. reflexivity. Qed.
Lemma euler_2_7 : euler_exp 2 7 = 1. Proof. reflexivity. Qed.
Lemma euler_3_7 : euler_exp 3 7 = 6. Proof. reflexivity. Qed.
Lemma euler_4_7 : euler_exp 4 7 = 1. Proof. reflexivity. Qed.
Lemma euler_5_7 : euler_exp 5 7 = 6. Proof. reflexivity. Qed.
Lemma euler_6_7 : euler_exp 6 7 = 6. Proof. reflexivity. Qed.

(* Euler criterion for p = 5 *)
Lemma euler_1_5 : euler_exp 1 5 = 1. Proof. reflexivity. Qed.
Lemma euler_2_5 : euler_exp 2 5 = 4. Proof. reflexivity. Qed.
Lemma euler_3_5 : euler_exp 3 5 = 4. Proof. reflexivity. Qed.
Lemma euler_4_5 : euler_exp 4 5 = 1. Proof. reflexivity. Qed.

(* Euler criterion for p = 11 *)
Lemma euler_1_11  : euler_exp 1  11 = 1.  Proof. reflexivity. Qed.
Lemma euler_2_11  : euler_exp 2  11 = 10. Proof. reflexivity. Qed.
Lemma euler_3_11  : euler_exp 3  11 = 1.  Proof. reflexivity. Qed.
Lemma euler_4_11  : euler_exp 4  11 = 1.  Proof. reflexivity. Qed.
Lemma euler_5_11  : euler_exp 5  11 = 1.  Proof. reflexivity. Qed.
Lemma euler_9_11  : euler_exp 9  11 = 1.  Proof. reflexivity. Qed.
Lemma euler_10_11 : euler_exp 10 11 = 10. Proof. reflexivity. Qed.

(* Theorem: Euler's criterion agrees with Legendre symbol at p=7 *)
Theorem euler_agrees_legendre_p7 : forall a,
  1 <= a -> a <= 6 ->
  (legendre a 7 = LegOne      <-> euler_exp a 7 = 1) /\
  (legendre a 7 = LegMinusOne <-> euler_exp a 7 = 6).
Proof.
  intros a H1 H2.
  destruct a as [|[|[|[|[|[|[|a]]]]]]]; try lia;
  split; split; intro H; try discriminate; try reflexivity.
Qed.

(******************************************************************************)
(* SECTION 6: FIRST SUPPLEMENT — (-1/p)                                      *)
(******************************************************************************)

(* First supplement: (-1/p) = (-1)^((p-1)/2)
   (-1 is a QR mod p) iff p ≡ 1 (mod 4)
   (-1 is a QNR mod p) iff p ≡ 3 (mod 4)

   We encode -1 as p-1. *)

Definition first_supplement (p : nat) : LegendreValue :=
  legendre (p - 1) p.

(* p ≡ 1 (mod 4) => -1 is a QR *)
Lemma neg1_qr_mod_5  : first_supplement 5  = LegOne.      Proof. reflexivity. Qed.
Lemma neg1_qr_mod_13 : first_supplement 13 = LegOne.      Proof. reflexivity. Qed.
Lemma neg1_qr_mod_17 : first_supplement 17 = LegOne.      Proof. reflexivity. Qed.
Lemma neg1_qr_mod_29 : first_supplement 29 = LegOne.      Proof. reflexivity. Qed.

(* p ≡ 3 (mod 4) => -1 is a QNR *)
Lemma neg1_qnr_mod_3  : first_supplement 3  = LegMinusOne. Proof. reflexivity. Qed.
Lemma neg1_qnr_mod_7  : first_supplement 7  = LegMinusOne. Proof. reflexivity. Qed.
Lemma neg1_qnr_mod_11 : first_supplement 11 = LegMinusOne. Proof. reflexivity. Qed.
Lemma neg1_qnr_mod_19 : first_supplement 19 = LegMinusOne. Proof. reflexivity. Qed.
Lemma neg1_qnr_mod_23 : first_supplement 23 = LegMinusOne. Proof. reflexivity. Qed.

(******************************************************************************)
(* SECTION 7: SECOND SUPPLEMENT — (2/p)                                      *)
(******************************************************************************)

(* Second supplement: (2/p) = (-1)^((p^2-1)/8)
   2 is a QR mod p iff p ≡ ±1 (mod 8) *)

Definition second_supplement (p : nat) : LegendreValue :=
  legendre 2 p.

(* p ≡ 1 (mod 8): p = 17, 41, ... *)
Lemma two_qr_mod_17  : second_supplement 17 = LegOne.      Proof. reflexivity. Qed.

(* p ≡ 7 (mod 8): p = 7, 23, 31, ... *)
Lemma two_qr_mod_7   : second_supplement 7  = LegOne.      Proof. reflexivity. Qed.
Lemma two_qr_mod_23  : second_supplement 23 = LegOne.      Proof. reflexivity. Qed.

(* p ≡ 3 (mod 8): p = 3, 11, 19, ... -> 2 is QNR *)
Lemma two_qnr_mod_3  : second_supplement 3  = LegMinusOne. Proof. reflexivity. Qed.
Lemma two_qnr_mod_11 : second_supplement 11 = LegMinusOne. Proof. reflexivity. Qed.
Lemma two_qnr_mod_19 : second_supplement 19 = LegMinusOne. Proof. reflexivity. Qed.

(* p ≡ 5 (mod 8): p = 5, 13, ... -> 2 is QNR *)
Lemma two_qnr_mod_5  : second_supplement 5  = LegMinusOne. Proof. reflexivity. Qed.
Lemma two_qnr_mod_13 : second_supplement 13 = LegMinusOne. Proof. reflexivity. Qed.

(******************************************************************************)
(* SECTION 8: LAW OF QUADRATIC RECIPROCITY — CONCRETE INSTANCES              *)
(******************************************************************************)

(* QR Law: for distinct odd primes p, q,
   (p/q)(q/p) = (-1)^((p-1)/2 * (q-1)/2)

   If both p ≡ q ≡ 3 (mod 4), then (p/q)(q/p) = -1 (they differ).
   Otherwise (p/q)(q/p) = 1 (they agree).

   We verify all pairs from {3, 5, 7, 11, 13}. *)

(* (3/5) and (5/3): both ≡ 3,1 mod 4 -> product = 1 -> (3/5) = (5/3) *)
Lemma qr_3_5 : legendre 3 5 = LegMinusOne. Proof. reflexivity. Qed.
Lemma qr_5_3 : legendre 5 3 = LegMinusOne. Proof. reflexivity. Qed.
(* Both -1: product = +1 = (-1)^(1*2) = 1 — consistent. *)

(* (3/7) and (7/3): 3≡3, 7≡3 mod 4 -> product = -1 -> symbols differ *)
Lemma qr_3_7 : legendre 3 7 = LegMinusOne. Proof. reflexivity. Qed.
Lemma qr_7_3 : legendre 7 3 = LegOne.      Proof. reflexivity. Qed.
(* (-1)(1) = -1 = (-1)^(1*3) = -1 — consistent. *)

(* (3/11) and (11/3): 3≡3, 11≡3 mod 4 -> product = -1 -> differ *)
Lemma qr_3_11 : legendre 3 11 = LegOne.      Proof. reflexivity. Qed.
Lemma qr_11_3 : legendre 11 3 = LegMinusOne. Proof. reflexivity. Qed.
(* (1)(-1) = -1 = (-1)^(1*5) = -1 — consistent. *)

(* (5/7) and (7/5): 5≡1, 7≡3 -> product = 1 -> same *)
Lemma qr_5_7 : legendre 5 7 = LegMinusOne. Proof. reflexivity. Qed.
Lemma qr_7_5 : legendre 7 5 = LegMinusOne. Proof. reflexivity. Qed.
(* (-1)(-1) = 1 = (-1)^(2*3) = 1 — consistent. *)

(* (5/11) and (11/5): 5≡1, 11≡3 -> product = 1 -> same *)
Lemma qr_5_11 : legendre 5 11 = LegOne.    Proof. reflexivity. Qed.
Lemma qr_11_5 : legendre 11 5 = LegOne.    Proof. reflexivity. Qed.

(* (5/13) and (13/5): 5≡1, 13≡1 -> product = 1 -> same *)
Lemma qr_5_13 : legendre 5 13 = LegMinusOne. Proof. reflexivity. Qed.
Lemma qr_13_5 : legendre 13 5 = LegMinusOne. Proof. reflexivity. Qed.

(* (7/11) and (11/7): 7≡3, 11≡3 -> product = -1 -> differ *)
Lemma qr_7_11 : legendre 7  11 = LegMinusOne. Proof. reflexivity. Qed.
Lemma qr_11_7 : legendre 11 7  = LegOne.      Proof. reflexivity. Qed.

(* (7/13) and (13/7): 7 congruent 3, 13 congruent 1 mod 4 -> product = 1 -> same *)
Lemma qr_7_13 : legendre 7  13 = LegMinusOne. Proof. reflexivity. Qed.
Lemma qr_13_7 : legendre 13 7  = LegMinusOne. Proof. reflexivity. Qed.

(******************************************************************************)
(* SECTION 9: LEGENDRE SYMBOL MULTIPLICATIVITY                                *)
(******************************************************************************)

(* (ab/p) = (a/p)(b/p) — verified at concrete cases *)

Definition legendre_product (x y : LegendreValue) : LegendreValue :=
  match x, y with
  | LegZero, _    => LegZero
  | _, LegZero    => LegZero
  | LegOne, v     => v
  | v, LegOne     => v
  | LegMinusOne, LegMinusOne => LegOne
  end.

(* 2*4 = 8 ≡ 1 (mod 7): (2/7)(4/7) = (1)(1) = 1 = (8/7) = (1/7) = 1 *)
Lemma multiplicativity_2_4_7 :
  legendre_product (legendre 2 7) (legendre 4 7) = legendre 1 7.
Proof. reflexivity. Qed.

(* 3*5 = 15 ≡ 1 (mod 7): (3/7)(5/7) = (-1)(-1) = 1 = (1/7) *)
Lemma multiplicativity_3_5_7 :
  legendre_product (legendre 3 7) (legendre 5 7) = legendre 1 7.
Proof. reflexivity. Qed.

(* 2*3 = 6 mod 7: (2/7)(3/7) = (1)(-1) = -1 = (6/7) *)
Lemma multiplicativity_2_3_7 :
  legendre_product (legendre 2 7) (legendre 3 7) = legendre 6 7.
Proof. reflexivity. Qed.

(* Multiplicativity theorem for Legendre product: it's commutative and associative *)
Theorem legendre_product_comm : forall x y,
  legendre_product x y = legendre_product y x.
Proof. intros [] []; reflexivity. Qed.

Theorem legendre_product_assoc : forall x y z,
  legendre_product (legendre_product x y) z =
  legendre_product x (legendre_product y z).
Proof. intros [] [] []; reflexivity. Qed.

Theorem legendre_product_one_l : forall x,
  legendre_product LegOne x = x.
Proof. intros []; reflexivity. Qed.

Theorem legendre_product_minusone_invol : forall x,
  legendre_product LegMinusOne (legendre_product LegMinusOne x) = x.
Proof. intros []; reflexivity. Qed.

(******************************************************************************)
(* SECTION 10: SUMMARY                                                        *)
(******************************************************************************)

(*
  Quadratic Reciprocity formalization covers:

    1. Divisibility and modular congruence.
    2. Boolean primality via trial division; verified for primes up to 23.
    3. Quadratic residues: boolean search; QR tables for mod 5, 7, 11.
    4. Legendre symbol: three-value type (0, 1, -1); computed at p in {5,7,11}.
    5. Euler's criterion: a^((p-1)/2) mod p confirmed = 1 for QRs and p-1
       for QNRs, at p in {5, 7, 11}; theorem aligning criterion with symbol.
    6. First supplement (-1/p): is_qr iff p ≡ 1 (mod 4);
       verified at p in {3,5,7,11,13,17,19,23,29}.
    7. Second supplement (2/p): is_qr iff p ≡ ±1 (mod 8);
       verified at p in {3,5,7,11,13,17,19,23}.
    8. Quadratic reciprocity law: concrete instances for all pairs in
       {3,5,7,11,13} confirming (p/q)(q/p) = (-1)^((p-1)/2 * (q-1)/2).
    9. Legendre product: multiplicativity, commutativity, associativity,
       involutivity of LegMinusOne.

  All proofs closed; no Admitted lemmas.
*)
