(** * Preface: Welcome to Analog Circuit Design and Analysis in Coq *)


(** This is the entry point to Circuit Analysis in Coq, this volume's validation work is exclusively focused on linear circuits, primarily involving the analysis of resistive circuits. *)

(** * Overall *)

(** The values of current, voltage, and resistance in the circuit are represented using real numbers in Coq. Therefore, it is necessary to import the [Real] library in Coq. Correspondingly, we attempt to represent the series-parallel structure of the circuit using [Lists] in Coq. In addition, the [Lra] [ssreflect] library needs to be imported, as the automated proof strategies within this library can assist us in verifying the properties of the circuit. *)

From Coq Require Import Reals Lra Lia ssreflect.
Require Import Coq.Lists.List.
Import ListNotations.

(** We will develop the foundational Coq verification for the analysis of small-signal analog circuits, resistor equivalence, and circuit equivalence separately. In the future, we plan to delve deeper into the analysis of analog circuits, including the incorporation of capacitors and inductors, analyzing power supply equivalence, and so forth. *)


(** * Section A : Circuit Analytic Techniques *)

(** In the following analytic techniques, only linear circuits will be considered. This means that the techniques apply only to small-signal models and circuits. This does not represent a serious limitation since much of the performance of analog circuits can be characterized by small-signal analysis. *)

Section Ac_analysis.
Open Scope R.

(** To simplify some symbolic derivation processes, we introduce an Ltac in Coq that addresses various issues related to n-ary functions not being equal to zero. When x1 > 0,...,xn > 0; we can use [solve_neq0_by_gt0] to prove f(x1, ..., xn) <> 0. *)

Ltac solve_neq0_by_gt0 :=
  repeat
    match goal with
    | |- ?r <> 0 => apply not_eq_sym, Rlt_not_eq
    | |- 0 < ?r1 + ?r2 => apply Rplus_lt_0_compat
    | |- 0 < ?r1 * ?r2 => apply Rmult_lt_0_compat
    end; auto.

(** * A_1 Chain-type Circuit Analysis *)

Section A1. 

(** In many cases, the analog small-signal circuit can
quickly be analyzed by a simple chain-type calculation. To consider Fig_A1, If we want to find [vout/vin] it is a simple matter to express this transfer function in a chain form. *)

Variable vout vin v1 gm R1 R2 R3 : R.

(** In chain 1, we get an equation between v1 and vin: *)

Hypothesis circl1 : v1 / vin = R2 / (R1 + R2).

(** In chain 2, Similarly, we get an equation about vout: *)

Hypothesis circl2 : vout  = - gm * v1 * R3.

(** On this basis, it is straightforward to prove the validity of the transfer function [transfer_f1]. *)

Lemma transfer_f1: vout / vin = - gm * R2 * R3 / (R1 + R2).
Proof.
  replace (- gm * R2 * R3 / (R1 + R2)) with (- gm * R3 * (R2 / (R1 + R2))) by lra.
  rewrite -circl1.
  replace (- gm * R3 * (v1 / vin)) with (- gm * v1 * R3 / vin) by lra.
  rewrite -circl2.
  reflexivity. 
Qed.

End A1.

(** * A_2 Nodal Analysis of an Analog Circuit *)

Section A2.

(** In more complex circuits, there is generally more than one signal path from the input to the output. In that case, a more systematic method of writing a set of linear equations that describe the circuit is required. Two well-known methods use nodal and mesh equations. They are based on Kirchhoff’s laws, which state the sum of the currents flowing into a node must be equal to zero and the sum of the voltage drops around a mesh must be equal to zero. *)

(** Consider the circuit of Fig_A2, The objective is to find [vout]/[iin]. *)
  
Variable i_in R1 v1 R2 gm R3 vout : R. 
Definition G1 := 1 / R1.
Definition G2 := 1 / R2.
Definition G3 := 1 / R3.

(** ptIA, ptIB: List the equations for the input and output currents at nodes A and B. *)

Hypothesis ptIA : i_in = (G1 + G2) * v1 - G2 * vout.
Hypothesis ptIB : 0 = (gm - G2) * v1 + (G2 + G3) * vout.

(** The desired transfer function is given below as [vout / i_in], Building upon this, prove the validity of the transfer function [transfer_f2] in Coq. *)

Lemma transfer_f2 : i_in <> 0 -> G1 > 0 -> G2 > 0 -> G3 > 0 -> gm > 0 ->
     vout / i_in = (G2 - gm) / (G1 * G2 + G1 * G3 + G2 * G3 + gm * G2).
Proof.
intros Hi Hr1 Hr2 Hr3 Hgm. 
(** For ptIA, multiply both sides of the equation by (gm - G2). *)
have h1 : (gm - G2) * i_in = (gm - G2) * (G1 + G2) * v1 - (gm - G2) * G2 * vout.
rewrite ptIA; lra.
(** For ptIB, multiply both sides of the equation by (G1 + G2). *) 
have h2 : 0 = (gm - G2) * (G1 + G2) * v1 + (G2 + G3) * (G1 + G2)  * vout.
(** For ptIB, multiply both sides of the equation by (G1 + G2). *)
replace ((gm - G2) * (G1 + G2) * v1 + (G2 + G3) * (G1 + G2) * vout) with 
((G1 + G2) * ((gm - G2) * v1 + (G2 + G3) * vout)) by lra.
rewrite -ptIB; lra.
(** Add both sides of the equations for h1, h2, denote the result as h3. *)
have h3 : (gm - G2) * (G1 + G2) * v1 = - (G2 + G3) * (G1 + G2) * vout by lra.
rewrite h3 in h1. 
(** After simplification, the proof is completed. *)
field_simplify_eq. lra. split.   
solve_neq0_by_gt0. lra. 
Qed. 

End A2.

(** * A_3 Mesh Analysis of an Analog Circuit *)

Section A3. 

(** Consider the circuit of Fig_A3. We wish to solve for the transfer function, vout/vin by mesh analysis. *)

Variable vin vout ia ib R1 R2 R3 rm: R.

(** Defining two mesh currents [ia] and [ib], we can derive two mesh equations using Kirchhoff's current law. *)

Hypothesis Mesh1 : vin = (R1 + R2) * ia + R1 * ib.
Hypothesis Mesh2 : vin = (R1 - rm) * ia + (R1 + R3) * ib.

(** We obtain an expression for [vout] in terms of [ia]. *) 

Hypothesis Mesh3 : vout = - rm * ia.

(** By eliminating the intermediary variables [ia] and [ib], we can verify the correctness of the transfer function transfer_f3 in Coq. The proof strategy is essentially similar to Lemma 'transfer_f2', as detailed in Section A2. *)

Lemma transfer_f3 :  vin <> 0 -> R1 > 0 -> R2 > 0 -> R3 > 0 -> rm > 0 ->
     vout / vin = - rm * R3 / (R1 * R2 + R1 * R3 + R2 * R3 + rm * R1).
Proof.
intros.
have h0 : ia = R3 * vin / (R1 * R2 + R1 * R3 + R2 * R3 + rm * R1).
apply Rmult_eq_compat_l with (r:= (R1+R3)) in Mesh1. 
apply Rmult_eq_compat_l with (r:= R1) in Mesh2.
have Mesh1' : R1 * (R1 + R3) * ib = (R1 + R3) * vin - (R1 + R3) * (R1 + R2) * ia.
lra.
have Mesh2' : R1 * (R1 + R3) * ib = R1 * vin - R1 * (R1 - rm) * ia. lra.
rewrite Mesh1' in Mesh2'.
have h1 : R3 * vin = (R1 * R2 + R1 * R3 + R2 * R3 + rm * R1) * ia. lra.
rewrite h1. field. 
solve_neq0_by_gt0.
rewrite Mesh3 h0.
field. split. solve_neq0_by_gt0.
lra.
Qed.

End A3.

(** * A_4 Combined Approach to Analyzing an Analog Circuit *)

Section A4. 

(** The circuit shown in Fig_A4 is used to model a current source. The objective of this example is to find the small-signal output resistance [rout] defined as [vo/io]. *)

Variable i iout Ai v1 vout R1 R2 R3 R4: R.

(** By employing the nodal analysis and mesh analysis methods introduced in the preceding two sections, expressions for [iout], [i] and [v1] in terms of the known parameters are obtained. *)
  
Definition rout := vout / iout.
Hypothesis C1 : iout = Ai * i + (vout - v1) / R4.
Hypothesis C2 : i = - R3 * iout / (R1 + R2 + R3).
Hypothesis Cv : v1 = iout * (R3 * R1 + R3 * R2) / (R1 + R2 + R3).

(** Identify an expression for [iout] solely in terms of [iout] [vout], and perform multiple substitutions of known quantities. Eventually, we can formulate the lemma [solve_rout] to verify the correctness of the expression for [rout]. *) 

Lemma solve_rout : iout <> 0 -> R1 > 0 -> R2 > 0 -> R3 > 0 -> R4 > 0 ->
     rout = (R4 * (R1 + R2 + R3) + R3 * R4 * Ai + R3 * (R1 + R2)) / (R1 + R2 + R3).
Proof.
  intros. unfold rout.
  (** Substitute [C2] and [Cv] into [C1], yielding a new expression for [iout].*)
  have hvi : iout = Ai * (- R3 * iout / (R1 + R2 + R3)) + (vout - (iout * (R3 * R1 + R3 * R2) / (R1 + R2 + R3))) / R4.
  rewrite -C2 -Cv. assumption.
  field_simplify_eq; try lra. 
  (** Replace [iout] in hvi with [C1], and multiply both sides of the equation by 
[ (R1+R2+R3)× R4] to bring it closer to the proof target. *)
  apply Rmult_eq_compat_l with (r:= ((R1 + R2 + R3) * R4)) in hvi.
  rewrite Rmult_plus_distr_l in hvi. 
  field_simplify ((R1 + R2 + R3) * R4 * (Ai * (- R3 * iout / (R1 + R2 + R3))))in hvi.
  have h0 : (R1 + R2 + R3) * R4 *
  ((vout - iout * (R3 * R1 + R3 * R2) / (R1 + R2 + R3)) /
  R4) = (R1 + R2 + R3) * vout - (R3 * R1 + R3 * R2) * iout.
  field.
  split; try lra. rewrite h0 in hvi. lra. lra.   
Qed.

End A4.

(** * A_5 Analysis of a Differential Amplifier *)

Section A5.  

(** A differential amplifier is shown in Fig_A5, The op amp has a finite voltage gain of [Av], an infinite input resistance, and a zero output resistance. Find [vo] as a function of [v1] and [v2]. *)

Variable Av va vb v1 v2 vout R1 R2 R3 R4 : R.

(** By analyzing the circuit, the following equation can be derived: *)

Hypothesis hv : vout = Av * (vb - va).
Hypothesis h1 : vb = (R4/ (R3 + R4)) * v2.
Hypothesis h2 : va = (R2/ (R1+ R2)) * v1 + (R1/ (R1+ R2)) * vout.

(** Observing the expression for [vout], we find: If [R3] / [R4] is equal to [R1] / [R2], then the amplifier is differential and the influence of the finite op amp voltage gain [Av] is given by 'Lemma solve_vout': *)

(** Primary Proof Strategy : *)
(** (1) Substitute [vb] and [va] separately into the expression for [vout] to obtain the expression for [vout]; *)
(** (2) Denote the expression obtained in step 1 as [hvo] and proceed with simplification. *)
  
Lemma solve_vout : R1 > 0 -> R2 > 0 -> Av > 0 ->
     vout = Av / (1 + Av * R1 / (R1 + R2)) * 
         ( R4 / (R3 + R4) * v2 - R2 / (R1 + R2) * v1).
Proof.
intros.
have hvo : vout = Av * (R4 / (R3 + R4) * v2 - R2 / (R1 + R2) * v1 - R1 / (R1 + R2) * vout). 
rewrite -h1. replace (vb - R2 / (R1 + R2) * v1 - R1 / (R1 + R2) * vout) with 
  (vb - (R2 / (R1 + R2) * v1 + R1 / (R1 + R2) * vout)) by lra.
  rewrite -h2.
  apply hv.
  rewrite Rmult_minus_distr_l in hvo. 
  replace (Av / (1 + Av * R1 / (R1 + R2)) *
(R4 / (R3 + R4) * v2 - R2 / (R1 + R2) * v1)) with (Av * (R4 / (R3 + R4) * v2 - R2 / (R1 + R2) * v1) / (1 + Av * R1 / (R1 + R2)) ) by lra.
  have h3 : Av * (R4 / (R3 + R4) * v2 - R2 / (R1 + R2) * v1) = vout + Av * (R1 / (R1 + R2) * vout).  lra. rewrite h3. field.
  split; try lra.  
  solve_neq0_by_gt0.
Qed.

End A5.

(** * Section B :  Coq Verification of Circuit Equivalence *)

Section Circuit_eq.  
Open Scope list_scope. 

(** * B1 Coq Description of Circuit Structure *)

(** Attempting to define series and parallel structures containing simple resistors using the [Fixpoint] function in Coq. *)

(** (1) Series Circuit *)

Fixpoint Series_res (l: list R) : R :=  
  match l with  
  | nil => 0 
  | ls :: l' => ls + (Series_res l')  
  end.
  
(** Now we check and compute the following series circuit with 5 resistors This serves as an illustration of the effectiveness of the series structure we have defined. *)
  
Check (Series_res [1;2;3;4;5]).

Compute (Series_res [1;2;3]).

(** (2) Parallel Circuit *)

(** We observe that: an additional intermediary function 'Series_parl_aux' was introduced during the definition of the parallel structure. *)

Fixpoint Series_parl_aux  (l: list R) : R :=  
  match l with  
  | nil => 1 
  | ls :: l' => (ls * (Series_parl_aux l')) 
  end.
  
Definition Series_parl (l: list R) : R := 
  (Series_parl_aux  l) / (Series_res  l).
  
(** Similarly, Now we check and compute the following parallel circuit. *)   
  
Check (Series_parl  [1;2;3;4;5]). 
 
Compute (Series_parl  [1;2;3]).
   
Lemma Series_parl_right : Series_parl  [1;2;3] = 1.
Proof.
compute. field.
Qed.

(** Now we define a simpler notation for Series_res and Series_parl, Designating them as [Sr] and [Sp]. in subsequent sections, we will use these notations to represent series and parallel circuits, respectively. *)

Definition Sr := Series_res.
Definition Spa := Series_parl_aux.
Definition Sp := Series_parl.

(** From this, we can verify that the series circuit and the parallel circuit as shown in the Fig_B1 are equivalent. That is, a series circuit with 2 ohms and 3 ohms is equivalent to a parallel circuit with 10 ohms and 10 ohms. We can prove its correctness in Coq. *)

Lemma res_eq_hold : Sr [2;3] = Sp [10; 10].
Proof.
compute. field.
Qed.

(** Voltage Division Formula for Series Resistors *)

Definition partial_Uk (U Rk : R) (Rl: list R) : R :=
   Rk / (Sr Rl) * U.
   
Lemma partial_Uk_hold : partial_Uk 8 3 [1;2;3] = 4.
Proof. compute. field. Qed.
     
(** Current Division Formula for Parallel Resistors *)

(** We further validated the correctness of the voltage division and current division formulas through Lemmas 'partial_Uk_hold' and 'partial_ik_hold'. *)

Definition condG (r : R):= 1 / r. 

Definition Geq_Series_cond (Gl: list R) : R :=  
   Series_res Gl.
   
Compute Geq_Series_cond [1;1/2;1/3].

Definition partial_ik (i Gk : R) (Gl: list R) : R :=
   Gk / (Geq_Series_cond Gl) * i.
   
Lemma partial_ik_hold : partial_ik 1 (1/3)  [1;1/2;1/3] = 2 / 11.
Proof. compute. field. Qed.

(** * B2 The Application of Resistor Equivalence *)

(** We design two examples of varying difficulty to demonstrate that formal verification of circuit equivalence in Coq is feasible using the circuit structures we designed. *)

(** (1) A parallel combination of 4-ohm and 4-ohm resistors, followed by a series connection with a 2-ohm resistor, is equivalent to a single 4-ohm resistor. *)

Lemma res_eq_hold_app : Sr [2 ; (Sp [4;4])] = 4.
Proof. compute; field. Qed.

(** (2) The circuit shown in Fig_B2, Verify the circuit equivalence between Figure B2(a) and Figure B2(b), with an equivalent resistance of [1.5] ohms. *)

Lemma res_eq_hold_ext : Sp [ 3; ( Sr [(Sp [ 4 ; (Sr [2 ; (Sp [4;4])])]) ; (Sp [2 ; 2]) ] ) ]= 3/2.
Proof.
compute. field.
Qed.

(** Through this example, we can observe that manually analyzing and verifying circuit equivalence can be cumbersome and error-prone. However, with the aid of Coq, we can describe these circuit structures more intuitively and clearly. Additionally, it becomes easier to verify their circuit equivalence. This illustrates the effectiveness and feasibility of using Coq for circuit analysis. *)

(** * B3 triangle and Y-shaped circuit equivalence verification *)

(** In this section, we will verify a classic circuit equivalence problem in Coq: the equivalence verification of a triangle circuit and a Y-shaped circuit. *)

(** Initially, formulate the circuit equations in Coq based on Kirchhoff's laws and Ohm's law. *)

Variable i1 i2 i3 u12 u13 u23 r12 r13 r23 r1 r2 r3 : R.
Hypothesis KCL1 : i3 = i1 + i2.
Hypothesis KVL1 : u12 + u23 - u13 = 0.
Hypothesis KCL_OL1 : i1 = u13/r13 + u12 / r12.
Hypothesis KCL_OL2 : i2 = u23/r23 - u12 / r12.
Hypothesis KVL2 : u13 = r1 * i1 + r3 * i3.
Hypothesis KVL3 : u23 = r2 * i2 + r3 * i3.

(** Subsequently, by substituting the expression [KCL_OL1] into [KCL1] and [KCL_OL2] into [KVL1], expressions for [u13] and [u23] can be obtained as Lemma 'simpl_u13' and Lemma simpl_u23, respectively. *)

Lemma simp_u13 : r12 > 0 -> r13 > 0 -> r23 > 0 ->  u13 = r13 * (r12 + r23) / 
      (r12 + r13 + r23) * i1 + r13 * r23 / (r12 + r13 + r23) * i2. 
Proof.
intros Hr1 Hr2 Hr3.
assert (u12 = u13- u23). lra.
have pi1 : i1 = (1/r13 + 1/r12) * u13 - (1/r12) * u23.
field_simplify_eq. rewrite KCL_OL1. rewrite H. field.
lra. lra.
have pi2 : i2 = - (1/r12) * u13 + (1/r23 + 1/r12) * u23.
field_simplify_eq. rewrite KCL_OL2. rewrite H. field.
lra. lra.
apply Rmult_eq_compat_l with ( r:= ((r12 + r23) /r23) ) in pi1. 
have pem : (r12 + r23) / r23 * i1 + i2 = (r12 + r23) / r23 *
      ((1 / r13 + 1 / r12) * u13 - 1 / r12 * u23) - (1 / r12) * u13 + (1 / r23 + 1 / r12) * u23 by lra.
field_simplify_eq in pem. lra.
apply Rmult_eq_reg_l with (r := r12). field_simplify_eq. lra.
lra. lra.
Qed.

Lemma simp_u23 : r12 > 0 -> r13 > 0 -> r23 > 0 ->  u23 = r13 * r23 / (r12 + r13 + r23) * i1 + r23 * (r12 + r13) / (r12 + r13 + r23) * i2.
Proof.
intros Hr1 Hr2 Hr3.
assert (u12 = u13- u23). lra.
have pi1 : i1 = (1/r13 + 1/r12) * u13 - (1/r12) * u23.
field_simplify_eq. rewrite KCL_OL1. rewrite H. field.
lra. lra.
have pi2 : i2 = - (1/r12) * u13 + (1/r23 + 1/r12) * u23.
field_simplify_eq. rewrite KCL_OL2. rewrite H. field.
lra. lra.
apply Rmult_eq_compat_l with ( r:= ((r12 + r13) /r13) ) in pi2. 
have pem :  i1 + (r12 + r13) / r13 * i2 = (1 / r13 + 1 / r12) * u13 - 1 / r12 * u23
  + (r12 + r13) / r13 *
      (- (1 / r12) * u13 + (1 / r23 + 1 / r12) * u23)  by lra.
field_simplify_eq in pem. lra. field_simplify_eq.
apply Rmult_eq_reg_l with (r := r12). field_simplify_eq. lra.
lra. lra.
Qed.

(** Then, formulate the two sets of linearly independent equations separately, obtaining three linearly independent equations. *)

Lemma eqvl_1 : r12 > 0 -> r13 > 0 -> r23 > 0 -> 
      (r13 * (r12 + r23) / (r12 + r13 + r23)) * i1 + 
      (r13 * r23 / (r12 + r13 + r23)) * i2 = (r1 + r3) * i1 + r3 * i2.
Proof.
intros Hr1 Hr2 Hr3.
have hp1 : u13 = (r1 + r3) * i1 + r3 * i2.
rewrite KVL2 KCL1. field.
rewrite simp_u13 in hp1; try lra.  
Qed.

Lemma eqvl_2 : r12 > 0 -> r13 > 0 -> r23 > 0 -> 
      (r13 * r23 / (r12 + r13 + r23)) * i1 + 
      (r23 * (r12 + r13) / (r12 + r13 + r23)) * i2 = r3 * i1 + (r2 + r3) * i2.
Proof.
intros Hr1 Hr2 Hr3.
have hp2 : u23 = r3 * i1 + (r2 + r3) * i2.
rewrite KVL3 KCL1. field.
rewrite simp_u23 in hp2; try lra.   
Qed.

(** On this basis, expressions between R1, R2, R3 and R12, R13, R23 can be derived. *)

Hypothesis linear_indep1 : r13 * (r12 + r23) / (r12 + r13 + r23) = r1 + r3. 
Hypothesis linear_indep2 : r13 * r23 / (r12 + r13 + r23) = r3.
Hypothesis linear_indep3 : r23 * (r12 + r13) / (r12 + r13 + r23) = r2 + r3.

Hypothesis r_gt_zero : r12 >0 /\ r13 > 0 /\ r23 > 0.

Lemma res_eq_r3 : r3 = r23 * r13 / (r12 + r13 + r23).
Proof.
  lra.
Qed.

Lemma res_eq_r1 : r1 = r13 * r12 / (r12 + r13 + r23).
Proof.
apply Rplus_eq_reg_r with (r := r3).
rewrite -linear_indep1. lra. 
Qed.
 
Lemma res_eq_r2 : r2 = r12 * r23 / (r12 + r13 + r23).
Proof.
apply Rplus_eq_reg_r with (r := r3).
rewrite -linear_indep3. lra.
Qed.

Lemma res_eq_r12 : r12 = (r1 * r2 + r2 * r3 + r3 * r1)/ r3.
Proof.
rewrite res_eq_r1 res_eq_r2 res_eq_r3.
field. lra. 
Qed.

Lemma res_eq_r13 : r13 = (r1 * r2 + r2 * r3 + r3 * r1)/ r2.
Proof.
rewrite res_eq_r1 res_eq_r2 res_eq_r3.
field. lra. 
Qed.

Lemma res_eq_r23 : r23 = (r1 * r2 + r2 * r3 + r3 * r1)/ r1.
Proof.
rewrite res_eq_r1 res_eq_r2 res_eq_r3.
field. lra. 
Qed.

(** Specifically, if r1, r2, r3 are equal and have a resistance value of 
r, then in this case, r12, r13, r23 are also equal and have a resistance value of 3r. The lemma 'circuit_eq_infer' proves the validity of this inference. *)

Lemma circuit_eq_infer (r : R) : r > 0 -> (r1 = r /\ r2 = r /\ r3 = r) 
      <-> (r12 =  3 * r /\ r13 = 3 * r /\ r23 = 3 * r).
Proof.
intros Hr.
split.
{ intros Hb. destruct Hb as [h1 h2]. destruct h2 as [h2 h3].
rewrite res_eq_r12 res_eq_r13 res_eq_r23.
rewrite h1 h2 h3.
repeat split; field; lra.
}
intros Hc. destruct Hc as [h1 h2]. destruct h2 as [h2 h3].
rewrite res_eq_r1 res_eq_r2 res_eq_r3.
rewrite h1 h2 h3.
repeat split; field; lra.
Qed.

(** * B4 The Application of triangle and Y-shaped circuit equivalence *)

(** Given the circuit shown in Fig_B3, determine the equivalent resistance [Rab] at point a and b under two different conditions. *)

(** Cond1: R12 = 1Ω, R23 = 2Ω, R13 = 3Ω, R4 = 1Ω, R5 = 3Ω. *)

(** Cond2: R12 = R23 = R13 = 9Ω, R4 = 1Ω, R5 = 3Ω. *)

(** In Coq, based on the given conditions and the description of series and parallel resistances, use two lemmas ' circuit_eq_app ' and ' circuit_eq_app' ' to complete the equivalence verification. *)

(** In cond1, the equivalent resistance [Rab] at point a and b is 47/33 Ω. *)

Lemma circuit_eq_app (r4 r5 : R): r12 = 1 -> r13 = 2 -> r23 = 3 -> r4 = 1 -> r5 = 3
     -> Sr [r1; (Sp [(Sr [r2 ; r4]) ; (Sr [r3 ; r5])])] = 47 / 33.
Proof.
  intros Hr1 Hr2 Hr3 Hr4 Hr5.
  have H1 : r1 = 1/3.
  rewrite res_eq_r1. rewrite Hr1 Hr2 Hr3. field.
  have H2 : r2 = 1/2.
  rewrite res_eq_r2. rewrite Hr1 Hr2 Hr3. field.
  have H3 : r3 = 1.
  rewrite res_eq_r3. rewrite Hr1 Hr2 Hr3. field.
  compute.
  rewrite H1 H2 H3 Hr4 Hr5.
  field.   
Qed.

(** In cond2, the equivalent resistance [Rab] at point a and b is 5.4 Ω. *)

Lemma circuit_eq_app' (r4 r5 : R): r12 = 9 -> r13 = r12 -> r23 = r12 -> r4 = 1 -> r5 = 3
     -> Sr [r1; (Sp [(Sr [r2 ; r4]) ; (Sr [r3 ; r5])])] = 5.4.
Proof.
  intros Hr1 Hr2 Hr3 Hr4 Hr5.
  have H1 : r1 = 3.
  rewrite res_eq_r1. rewrite Hr1 Hr2 Hr3. rewrite Hr1;  field.
  have H2 : r2 = 3.
  rewrite res_eq_r2. rewrite Hr1 Hr2 Hr3. rewrite Hr1;  field.
  have H3 : r3 = 3.
  rewrite res_eq_r3. rewrite Hr1 Hr2 Hr3. rewrite Hr1;  field.
  compute.
  rewrite H1 H2 H3 Hr4 Hr5.
  field_simplify_eq.
  compute. field.  
Qed.

(** Based on the given conditions and the description of series and parallel resistances, using two lemmas to accomplish the equivalence verification. Building upon this foundation, various linear circuits can be analyzed. *)
      
End Circuit_eq. 

End Ac_analysis.












