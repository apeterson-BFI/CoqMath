Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Fixpoint addn (n1 n2 : nat) :=
  match n1 with
  | O => n2
  | S n1' => S (addn n1' n2)
  end.

Fixpoint muln (n1 n2 : nat) :=
  match n1 with
  | O => O
  | S n1' => addn n2 (muln n1' n2)
  end.

Lemma addn_n_O : forall (n : nat), addn n O = n.
  induction n.
    reflexivity.

    simpl.
    rewrite IHn.
    reflexivity.
  Defined.

Lemma addn_Scomm : forall (n1 n2 : nat), addn (S n1) n2 = addn n1 (S n2).
  induction n1.
    intro n2.
    reflexivity.

    intro n2.
    simpl.
    rewrite <- IHn1.
    reflexivity.
  Defined.

Theorem addn_comm : forall (n1 n2 : nat), addn n1 n2 = addn n2 n1.
  induction n1.
    intro n2.
    rewrite addn_n_O.
    reflexivity.

    intro n2.
    rewrite <- addn_Scomm.
    simpl.
    rewrite IHn1.
    reflexivity.
  Defined.

Theorem addn_assoc : forall (n1 n2 n3 : nat), addn (addn n1 n2) n3 = addn n1 (addn n2 n3).
  induction n1.
    reflexivity.
    
    simpl.
    intros n2 n3.
    rewrite IHn1.
    reflexivity.
  Defined.

Lemma addn_n_mu_comm : forall (n1 n2 n3 : nat), addn n1 (addn n2 n3) = addn n2 (addn n1 n3).
  intros n1 n2 n3.
  rewrite <- addn_assoc.
  rewrite <- addn_assoc.
  rewrite (addn_comm n1 n2).
  reflexivity.
  Defined.

Lemma muln_n_Sm : forall (n1 n2 : nat), muln n1 (S n2) = addn n1 (muln n1 n2).
  induction n1.
    intro n2.
    reflexivity.

    intro n2.
    simpl.
    rewrite IHn1.
    rewrite addn_n_mu_comm.
    reflexivity.
  Defined.

Lemma muln_n_O : forall (n : nat), muln n O = O.
  induction n.
    reflexivity.

    simpl.
    assumption.
  Defined.

Theorem muln_comm : forall (n1 n2 : nat), muln n1 n2 = muln n2 n1.
  induction n1.
    intro n2.
    simpl.
    rewrite muln_n_O.
    reflexivity.

    intro n2.
    simpl.
    rewrite IHn1.
    rewrite muln_n_Sm.
    reflexivity.
  Defined.

Lemma addn_mdisthelp : forall (n1 n2 n3 n4 : nat), addn (addn n1 n2) (addn n3 n4) = addn (addn n1 n3) (addn n2 n4).
  intros n1 n2 n3 n4.
  rewrite (addn_assoc n1 n2 (addn n3 n4)).
  rewrite (addn_assoc n1 n3 (addn n2 n4)).
  rewrite <- (addn_assoc n3 n2 n4).
  rewrite (addn_comm n3 n2).
  rewrite -> (addn_assoc n2 n3 n4).
  reflexivity.
  Defined.

Theorem muln_dist_addn : forall (n1 n2 n3 : nat), muln n1 (addn n2 n3) = addn (muln n1 n2) (muln n1 n3).
  induction n1.
    reflexivity.

    simpl.
    intros n2 n3.
    rewrite IHn1.
    rewrite (addn_mdisthelp n2 n3 (muln n1 n2) (muln n1 n3)).
    reflexivity.
  Defined.

Theorem muln_ldist : forall (n1 n2 n3 : nat), muln (addn n1 n2) n3 = addn (muln n1 n3) (muln n2 n3).
  intros n1 n2 n3.
  rewrite muln_comm.
  rewrite (muln_comm n1 n3).
  rewrite (muln_comm n2 n3).
  rewrite (muln_dist_addn n3 n1 n2).
  reflexivity.
  Defined.

Theorem muln_assoc : forall (n1 n2 n3 : nat), muln (muln n1 n2) n3 = muln n1 (muln n2 n3).
  induction n1.
    simpl. 
    reflexivity.
    
    simpl.
    intros n2 n3.
    rewrite muln_ldist.
    rewrite <- IHn1.
    reflexivity.
  Defined.

Inductive int : Set :=
  | P : nat -> int
  | N : nat -> int.

Check nat_ind.

Fixpoint red0 (i : int) :=
  match i with
  | P O => P O
  | P (S n) => P n
  | N O => N O
  | N (S n) => N n
  end.

Axiom pz_equals_nz : P O = N O.

Fixpoint c_nat_int (n : nat) : int :=
  P n.

Fixpoint neg (i : int) :=
  match i with
  | P O => P O
  | P n => N n
  | N n => P n
  end.

Fixpoint inci (i : int) :=
  match i with
  | P n => P (S n)
  | N O => P (S O)
  | N (S n) => N n
  end.

Fixpoint deci (i : int) :=
  match i with
  | P O => N (S O)
  | P (S n) => P n
  | N n => N (S n)
  end.

Fixpoint sub_PPn (n1 n2 : nat) :=
  match n1 with
  | O => N n2
  | S n1' => 
    match n2 with
    | O => P n1
    | S n2' => sub_PPn n1' n2'
    end
  end.

Lemma subPPn_O : forall n : nat, sub_PPn n O = P n.
  induction n.
    simpl.
    rewrite pz_equals_nz.
    reflexivity.

    reflexivity.
  Defined.

Lemma subPPn_n : forall n : nat, sub_PPn n n = P O.
  induction n.
    simpl.
    rewrite pz_equals_nz.
    reflexivity.

    simpl.
    assumption.
  Defined.

Lemma subPP_Sn_Sm : forall n m : nat, sub_PPn (S n) (S m) = sub_PPn n m.
  intros n m.
  reflexivity.
  Defined.

Lemma subPP_inci : forall n m : nat, inci (sub_PPn n m) = sub_PPn (S n) m.
  induction n.
    destruct m; reflexivity.

    destruct m; try reflexivity.
    rewrite? subPP_Sn_Sm.
    rewrite IHn.
    reflexivity.
  Defined.

Fixpoint sub_PNn (n1 n2 : nat) :=
  match n1 with
  | O => P n2
  | S n1' => inci (sub_PNn n1' n2)
  end.

Lemma ps_eq_inc_P : forall n : nat, P (S n) = inci (P n).
  destruct n.
    reflexivity.

    reflexivity.
  Defined.

Lemma subPNn_O : forall n : nat, sub_PNn n O = P n.
  induction n.
    reflexivity.

    simpl.
    rewrite IHn.
    rewrite ps_eq_inc_P.
    reflexivity.
  Defined.

Lemma subPN_eq_Padd : forall n1 n2 : nat, sub_PNn n1 n2 = P (addn n1 n2).
  induction n1.
    reflexivity.

    simpl.
    intros n2.
    rewrite (ps_eq_inc_P (addn n1 n2)).
    rewrite IHn1.
    reflexivity.
  Defined.

Fixpoint sub_NPn (n1 n2 : nat) :=
  match n1 with
  | O => N n2
  | S n1' => deci (sub_NPn n1' n2)
  end.

Lemma ns_eq_dec_N : forall n : nat, N (S n) = deci (N n).
  destruct n.
    reflexivity.
    
    reflexivity.
  Defined.

Lemma subNPn_O : forall n : nat, sub_NPn n O = N n.
  induction n.
    reflexivity.
    
    simpl.
    rewrite IHn.
    rewrite ns_eq_dec_N.
    reflexivity.
  Defined.

Lemma subNP_eq_Nadd : forall n1 n2 : nat, sub_NPn n1 n2 = N (addn n1 n2).
  induction n1.
    reflexivity.

    simpl.
    intros n2.
    rewrite (ns_eq_dec_N (addn n1 n2)).
    rewrite IHn1.
    reflexivity.
  Defined.

Lemma subNPn_Sm : forall n m : nat, sub_NPn n (S m) = deci (sub_NPn n m).
  induction n; destruct m; try reflexivity.
  simpl.
  rewrite IHn.
  rewrite? subNPn_O.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
  Defined.


Fixpoint sub_NNn (n1 n2 : nat) :=
  match n1 with
  | O => P n2
  | S n1' =>
    match n2 with
    | O => N n1
    | S n2' => sub_NNn n1' n2'
    end
  end.

Lemma subNNn_O : forall n : nat, sub_NNn n O = N n.
  induction n.
    simpl.
    rewrite pz_equals_nz.
    reflexivity.

    reflexivity.
  Defined.

Lemma subNNn_n : forall n : nat, sub_NNn n n = P O.
  induction n.
    reflexivity.

    simpl.
    rewrite IHn.
    reflexivity.
  Defined.

Lemma subNNn_Sm : forall n m : nat, sub_NNn n (S m) = inci (sub_NNn n m).
  induction n; destruct m; try reflexivity.
  simpl.
  rewrite subNNn_O.
  reflexivity.

  simpl.
  rewrite IHn.
  reflexivity.
  Defined.

Fixpoint subi (i1 i2 : int) :=
  match i1, i2 with
  | P n1, P n2 => sub_PPn n1 n2
  | P n1, N n2 => sub_PNn n1 n2
  | N n1, P n2 => sub_NPn n1 n2
  | N n1, N n2 => sub_NNn n1 n2
  end.

Fixpoint addi (i1 i2 : int) :=
  match i1, i2 with
  | P n1, P n2 => sub_PNn n1 n2
  | P n1, N n2 => sub_PPn n1 n2
  | N n1, P n2 => sub_NNn n1 n2
  | N n1, N n2 => sub_NPn n1 n2
  end.

Lemma pos_add_ntoi : forall n1 n2 : nat, P (addn n1 n2) = addi (P n1) (P n2).
  induction n1.
    reflexivity.

    intro n2.
    simpl.
    rewrite ps_eq_inc_P.
    rewrite subPN_eq_Padd.
    reflexivity.
  Defined.

Lemma neg_add_ntoi : forall n1 n2 : nat, N (addn n1 n2) = addi (N n1) (N n2).
  induction n1.
    reflexivity.

    intro n2.
    simpl.
    rewrite ns_eq_dec_N.
    rewrite subNP_eq_Nadd.
    reflexivity.
  Defined.

Lemma addi_O_i : forall i : int, addi (P O) i = i.
  induction i.
    reflexivity.
    reflexivity.
  Defined.

Lemma addi_i_O : forall i : int, addi i (P O) = i.
  induction i.
    simpl.
    rewrite subPNn_O.
    reflexivity.
    
    simpl.
    rewrite subNNn_O.
    reflexivity.
  Defined.

Lemma addi_i_negi : forall i : int, addi i (neg i) = P O.
  induction i.
    simpl.
    induction n.
      reflexivity.
      
      rewrite subPPn_n.
      reflexivity.

    simpl.
    rewrite subNNn_n.
    reflexivity.
  Defined.

Lemma subi_i_i : forall i : int, subi i i = P O.
  induction i.
    simpl.
    rewrite subPPn_n.
    reflexivity.

    simpl.
    rewrite subNNn_n.
    reflexivity.
  Defined.

Lemma subi_O_i : forall i : int, subi (P O) i = neg i.
  induction i.
    induction n.
      simpl.
      rewrite pz_equals_nz.
      reflexivity.

      reflexivity.

    induction n.
      reflexivity.

      reflexivity.
  Defined.

Lemma subi_i_O : forall i : int, subi i (P O) = i.
  induction i.
    induction n.
      simpl.
      rewrite pz_equals_nz.
      reflexivity.

      reflexivity.
    induction n.
      rewrite <- pz_equals_nz.
      rewrite subi_i_i.
      reflexivity.

      simpl.
      rewrite ns_eq_dec_N.
      rewrite subNPn_O.
      reflexivity.
  Defined.
  
Lemma neg_inv_neg : forall i : int, neg (neg i) = i.
  destruct i.
    induction n; reflexivity.
    induction n.
      simpl.
      rewrite pz_equals_nz.
      reflexivity.

      reflexivity.
  Defined.

Lemma neg_inci_eq_deci_neg : forall i : int, neg (inci i) = deci (neg i).
  destruct i; destruct n; try reflexivity.
  Defined.

Lemma inci_deci_eq_i : forall i : int, inci (deci i) = i.
  destruct i;  induction n; try reflexivity; try (simpl; rewrite pz_equals_nz; reflexivity).
  Defined.

Lemma deci_inci_eq_i : forall i : int, deci (inci i) = i.
  destruct i; induction n; try reflexivity; try (simpl; rewrite pz_equals_nz; reflexivity).
  Defined.

Lemma addi_Pn_inciPm : forall n m : nat, addi (P n) (inci (P m)) = inci (addi (P n) (P m)).
  intros n m.
  simpl.
  rewrite? subPN_eq_Padd.
  rewrite <- addn_Scomm.
  reflexivity.
  Defined.

Lemma addi_Pn_inciNm : forall n m : nat, addi (P n) (inci (N m)) = inci (addi (P n) (N m)).
  intros.
  simpl.
  destruct n; destruct m; try reflexivity.
  rewrite subPPn_O.
  rewrite subPN_eq_Padd.
  rewrite addn_comm; simpl.
  reflexivity.

  rewrite subPP_Sn_Sm.
  rewrite subPP_inci.
  reflexivity.
  Defined.

Lemma addi_Nn_inciPm : forall n m : nat, addi (N n) (inci (P m)) = inci (addi (N n) (P m)).
  intros.
  simpl.
  rewrite subNNn_Sm.
  reflexivity.
  Defined.

Lemma addi_Nn_inciNm : forall n m : nat, addi (N n) (inci (N m)) = inci (addi (N n) (N m)).
  intros.
  destruct n; destruct m; try reflexivity.
  simpl.
  rewrite subNNn_O.
  rewrite subNPn_O.
  rewrite inci_deci_eq_i.
  reflexivity.
  simpl.
  rewrite inci_deci_eq_i.
  rewrite subNPn_Sm.
  reflexivity.
  Defined.

Lemma addi_i_incij : forall i j : int, addi i (inci j) = inci (addi i j).
  destruct i; destruct j.
  rewrite addi_Pn_inciPm; reflexivity.
  rewrite addi_Pn_inciNm; reflexivity.
  rewrite addi_Nn_inciPm; reflexivity.
  rewrite addi_Nn_inciNm; reflexivity.
  Defined.

Lemma addi_comm : forall i j : int, addi i j = addi j i.
