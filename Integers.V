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

Lemma addn_n_Sm : forall (n m : nat), addn n (S m) = S (addn n m).
  intros n m.
  rewrite <- addn_Scomm.
  reflexivity.
  Defined.

Lemma addn_Sn_m : forall (n m : nat), addn (S n) m = S (addn n m).
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

Lemma muln_Sn_m : forall (n1 n2 : nat), muln (S n1) n2 = addn n2 (muln n1 n2).
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

Lemma subPP_deci : forall n m : nat, deci (sub_PPn n m) = sub_PPn n (S m).
  induction n; destruct m; try reflexivity.
  rewrite subPP_Sn_Sm.
  rewrite? subPPn_O.
  reflexivity.
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

Lemma neg_PSn_eq_NSn : forall n : nat, neg (P (S n)) = N (S n).
  induction n; try reflexivity.
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

Lemma addi_Pn_Pm_comm : forall n m : nat, addi (P n) (P m) = addi (P m) (P n).
  intros.
  simpl.
  rewrite? subPN_eq_Padd.
  rewrite addn_comm.
  reflexivity.
  Defined.

Lemma subPPnm_eq_subNNmn : forall n m : nat, sub_PPn n m = sub_NNn m n.
  induction n; destruct m; try reflexivity.
  simpl; rewrite pz_equals_nz; reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
  Defined.

Lemma addi_Pn_Nm_comm : forall n m : nat, addi (P n) (N m) = addi (N m) (P n).
  intros.
  simpl.
  induction n; destruct m; try reflexivity.
  simpl; rewrite pz_equals_nz; reflexivity.
  simpl.
  rewrite subPPnm_eq_subNNmn.
  reflexivity.
  Defined.

Lemma addi_Nn_Pm_comm : forall n m : nat, addi (N n) (P m) = addi (P m) (N n).
  intros.
  simpl.
  rewrite subPPnm_eq_subNNmn.
  reflexivity.
  Defined.

Lemma addi_Nn_Nm_comm : forall n m : nat, addi (N n) (N m) = addi (N m) (N n).
  intros.
  simpl.
  rewrite? subNP_eq_Nadd.
  rewrite addn_comm.
  reflexivity.
  Defined.

Theorem addi_comm : forall i1 i2 : int, addi i1 i2 = addi i2 i1.
  destruct i1; destruct i2.
  rewrite addi_Pn_Pm_comm; reflexivity.
  rewrite addi_Pn_Nm_comm; reflexivity.
  rewrite addi_Nn_Pm_comm; reflexivity.
  rewrite addi_Nn_Nm_comm; reflexivity.
  Defined.

Lemma addi_Pn_deciPm : forall n m : nat, addi (P n) (deci (P m)) = deci (addi (P n) (P m)).
  induction n; destruct m; try reflexivity.
  simpl.
  rewrite subPPn_O.
  rewrite subPNn_O.
  rewrite deci_inci_eq_i.
  reflexivity.
  simpl.
  rewrite? subPN_eq_Padd.
  rewrite <- addn_Scomm.
  simpl.
  reflexivity.
  Defined.

Lemma addi_Pn_deciNm : forall n m : nat, addi (P n) (deci (N m)) = deci (addi (P n) (N m)).
  induction n; destruct m; try reflexivity.
  simpl.
  rewrite subPPn_O.
  reflexivity.
  simpl.
  rewrite subPP_deci.
  reflexivity.
  Defined.

Lemma addi_Nn_deciPm : forall n m : nat, addi (N n) (deci (P m)) = deci (addi (N n) (P m)).
  induction n; destruct m; try reflexivity.
  simpl.
  rewrite subNPn_Sm.
  rewrite subNPn_O.
  reflexivity.
  rewrite? ns_eq_dec_N.
  rewrite? ps_eq_inc_P.
  rewrite addi_i_incij.
  rewrite? deci_inci_eq_i.
  reflexivity.
  Defined.
  
Lemma addi_Nn_deciNm : forall n m : nat, addi (N n) (deci (N m)) = deci (addi (N n) (N m)).
  induction n; destruct m; try reflexivity.
  simpl.
  rewrite subNPn_Sm.
  reflexivity.
  rewrite? ns_eq_dec_N.
  simpl.
  rewrite subNPn_Sm.
  reflexivity.
  Defined.

Lemma addi_i_decij : forall i j : int, addi i (deci j) = deci (addi i j).
  destruct i as [p1 | n1]; destruct j as [p2 | n2].
  rewrite addi_Pn_deciPm; reflexivity.
  rewrite addi_Pn_deciNm; reflexivity.
  rewrite addi_Nn_deciPm; reflexivity.
  rewrite addi_Nn_deciNm; reflexivity.
  Defined.

Lemma addi_deci_j : forall i j : int, addi (deci i) j = deci (addi i j).
  intros i j.
  rewrite addi_comm.
  rewrite addi_i_decij.
  rewrite addi_comm.
  reflexivity.
  Defined.

Lemma addi_inci_j : forall i1 i2 : int, addi (inci i1) i2 = inci (addi i1 i2).
  intros i1 i2;
  rewrite addi_comm.
  rewrite addi_i_incij.
  rewrite (addi_comm i2 i1).
  reflexivity.
  Defined.

Lemma addi_inci_decj : forall i j : int, addi (inci i) (deci j) = addi i j.
  intros i j.
  rewrite addi_inci_j.
  rewrite addi_i_decij.
  rewrite inci_deci_eq_i.
  reflexivity.
  Defined.

Lemma addi_deci_incj : forall i j : int, addi (deci i) (inci j) = addi i j.
  intros i j.
  rewrite addi_comm.
  rewrite addi_inci_decj.
  rewrite addi_comm.
  reflexivity.
  Defined.

Lemma addi_PSn_j : forall (n : nat) (j : int), addi (P (S n)) j = inci (addi (P n) j).
  intros n j.
  rewrite ps_eq_inc_P.
  rewrite addi_inci_j.
  reflexivity.
  Defined.

Lemma addi_NSn_j : forall (n : nat) (j : int), addi (N (S n)) j = deci (addi (N n) j).
  intros n j.
  rewrite ns_eq_dec_N.
  rewrite addi_deci_j.
  reflexivity.
  Defined.

Lemma addi_i_PSn : forall (n : nat) (i : int), addi i (P (S n)) = inci (addi i (P n)).
  intros i n.
  rewrite ps_eq_inc_P.
  rewrite addi_i_incij.
  reflexivity.
  Defined.

Lemma addi_i_NSn : forall (n : nat) (i : int), addi i (N (S n)) = deci (addi i (N n)).
  intros i n.
  rewrite ns_eq_dec_N.
  rewrite addi_i_decij.
  reflexivity.
  Defined.

Lemma addi_assoc_PPP : forall n1 n2 n3 : nat, addi (addi (P n1) (P n2)) (P n3) = addi (P n1) (addi (P n2) (P n3)).
  induction n1; 
  destruct n2; 
  destruct n3;
  rewrite ?addi_O_i;
  rewrite ?addi_i_O;
  try reflexivity.
  rewrite ?addi_PSn_j.
  rewrite ?addi_i_PSn.
  rewrite ?addi_inci_j.
  rewrite ?addi_i_incij.
  rewrite IHn1.
  reflexivity.
  Defined.

Lemma addi_assoc_PPN : forall n1 n2 n3 :  nat, addi (addi (P n1) (P n2)) (N n3) = addi (P n1) (addi (P n2) (N n3)).
  induction n1;
  destruct n2;
  destruct n3;
  rewrite <- ?pz_equals_nz;
  rewrite ?addi_O_i;
  rewrite ?addi_i_O;
  try reflexivity.
  rewrite ?addi_PSn_j.
  rewrite ?addi_i_PSn.
  rewrite ?addi_i_NSn.
  rewrite ?addi_inci_j.
  rewrite ?addi_i_incij.
  rewrite ?addi_i_decij.
  rewrite ?inci_deci_eq_i.
  rewrite ?deci_inci_eq_i.
  rewrite IHn1.
  reflexivity.
  Defined.

Lemma addi_assoc_PNP : forall n1 n2 n3 : nat, addi (addi (P n1) (N n2)) (P n3) = addi (P n1) (addi (N n2) (P n3)).
  induction n1;
  destruct n2;
  destruct n3;
  rewrite <- ?pz_equals_nz;
  rewrite ?addi_O_i;
  rewrite ?addi_i_O;
  try reflexivity.
  rewrite ?addi_PSn_j.
  rewrite ?addi_NSn_j.
  rewrite ?addi_i_PSn.
  rewrite ?addi_i_NSn.
  rewrite ?inci_deci_eq_i.
  rewrite ?deci_inci_eq_i.
  rewrite IHn1.
  reflexivity.
  Defined.

Lemma addi_assoc_PNN : forall n1 n2 n3 : nat, addi (addi (P n1) (N n2)) (N n3) = addi (P n1) (addi (N n2) (N n3)).
  induction n1;
  destruct n2;
  destruct n3;
  rewrite <- ?pz_equals_nz;
  rewrite ?addi_O_i;
  rewrite ?addi_i_O;
  try reflexivity.
  rewrite ?addi_PSn_j.
  rewrite ?addi_NSn_j.
  rewrite ?addi_i_PSn.
  rewrite ?addi_i_NSn.
  rewrite ?addi_i_decij.
  rewrite ?inci_deci_eq_i.
  rewrite IHn1.
  reflexivity.
  Defined.

Lemma addi_assoc_NPP : forall n1 n2 n3 : nat, addi (addi (N n1) (P n2)) (P n3) = addi (N n1) (addi (P n2) (P n3)).
  induction n1;
  destruct n2;
  destruct n3;
  rewrite <- ?pz_equals_nz;
  rewrite ?addi_O_i;
  rewrite ?addi_i_O;
  try reflexivity.
  rewrite ?addi_PSn_j.
  rewrite ?addi_NSn_j.
  rewrite ?addi_i_PSn.
  rewrite ?addi_i_incij.
  rewrite ?addi_deci_j.
  rewrite inci_deci_eq_i.
  rewrite deci_inci_eq_i.
  rewrite addi_inci_j.
  rewrite IHn1.
  reflexivity.
  Defined.

Lemma addi_assoc_NPN : forall n1 n2 n3 : nat, addi (addi (N n1) (P n2)) (N n3) = addi (N n1) (addi (P n2) (N n3)).
  induction n1;
  destruct n2;
  destruct n3;
  rewrite <- ?pz_equals_nz;
  rewrite ?addi_O_i;
  rewrite ?addi_i_O;
  try reflexivity.
  rewrite ?addi_PSn_j.
  rewrite ?addi_NSn_j.
  rewrite ?addi_i_PSn.
  rewrite ?addi_i_NSn.
  rewrite ?addi_deci_j.
  rewrite ?addi_i_incij.
  rewrite ?addi_i_decij.
  rewrite ?addi_inci_j.
  rewrite IHn1.
  rewrite inci_deci_eq_i.
  rewrite deci_inci_eq_i.
  reflexivity.
  Defined.

Lemma addi_assoc_NNP : forall n1 n2 n3 : nat, addi (addi (N n1) (N n2)) (P n3) = addi (N n1) (addi (N n2) (P n3)).
  induction n1;
  destruct n2;
  destruct n3;
  rewrite <- ?pz_equals_nz;
  rewrite ?addi_O_i;
  rewrite ?addi_i_O;
  try reflexivity.
  rewrite ?addi_PSn_j.
  rewrite ?addi_NSn_j.
  rewrite ?addi_i_PSn.
  rewrite ?addi_i_NSn.
  rewrite ?addi_deci_j.
  rewrite ?addi_i_decij.
  rewrite ?addi_i_incij.
  rewrite ?inci_deci_eq_i.
  rewrite ?deci_inci_eq_i.
  rewrite IHn1.
  reflexivity.
  Defined.

Lemma addi_assoc_NNN : forall n1 n2 n3 : nat, addi (addi (N n1) (N n2)) (N n3) = addi (N n1) (addi (N n2) (N n3)).
  induction n1;
  destruct n2;
  destruct n3;
  rewrite <- ?pz_equals_nz;
  rewrite ?addi_O_i;
  rewrite ?addi_i_O;
  try reflexivity.
  rewrite ?addi_PSn_j.
  rewrite ?addi_NSn_j.
  rewrite ?addi_i_PSn.
  rewrite ?addi_i_NSn.
  rewrite ?addi_deci_j.
  rewrite ?addi_i_decij.
  rewrite IHn1.
  reflexivity.
  Defined.

Theorem addi_assoc : forall i1 i2 i3 : int, addi (addi i1 i2) i3 = addi i1 (addi i2 i3).
  destruct i1 as [n1 | n1]; 
  destruct i2 as [n2 | n2]; 
  destruct i3 as [n3 | n3].
  rewrite addi_assoc_PPP; reflexivity.
  rewrite addi_assoc_PPN; reflexivity.
  rewrite addi_assoc_PNP; reflexivity.
  rewrite addi_assoc_PNN; reflexivity.
  rewrite addi_assoc_NPP; reflexivity.
  rewrite addi_assoc_NPN; reflexivity.
  rewrite addi_assoc_NNP; reflexivity.
  rewrite addi_assoc_NNN; reflexivity.
  Defined.

Theorem addi_eq_subinj : forall i j : int, addi i (neg j) = subi i j.
  destruct i as [n1 | n1]; 
  destruct j as [n2 | n2];
  unfold subi;
  destruct n2;
  try reflexivity.
  simpl.
  rewrite subPNn_O.
  rewrite subPPn_O.
  reflexivity.
  simpl.
  rewrite subNNn_O.
  rewrite subNPn_O.
  reflexivity.
  Defined.

Lemma subi_PSn_j : forall (n : nat) (j : int), subi (P (S n)) j = inci (subi (P n) j).
  intros n j.
  rewrite <- ?addi_eq_subinj.
  rewrite addi_PSn_j.
  reflexivity.
  Defined.

Lemma subi_NSn_j : forall (n : nat) (j : int), subi (N (S n)) j = deci (subi (N n) j).
  intros n j.
  rewrite <- ?addi_eq_subinj.
  rewrite addi_NSn_j.
  reflexivity.
  Defined.

Lemma neg_Pn : forall (n : nat), neg (P n) = N n.
  destruct n.
  unfold neg.
  rewrite pz_equals_nz.
  reflexivity.
  reflexivity.
  Defined.

Lemma neg_Nn : forall (n : nat), neg (N n) = P n.
  destruct n.
  unfold neg.
  rewrite pz_equals_nz.
  reflexivity.
  reflexivity.
  Defined.

Lemma neg_deci_eq_inci_neg : forall i : int, neg (deci i) = inci (neg i).
  destruct i; destruct n; try reflexivity.
  unfold deci.
  rewrite ?neg_Pn.
  reflexivity.
  Defined.

Lemma subi_i_PSn : forall (i : int) (n : nat), subi i (P (S n)) = deci (subi i (P n)).
  intros i n.
  rewrite <- ?addi_eq_subinj.
  rewrite <- addi_deci_j.
  rewrite ?neg_Pn.
  rewrite addi_i_NSn.
  rewrite addi_deci_j.
  reflexivity.
  Defined.

Lemma subi_i_NSn : forall (i : int) (n : nat), subi i (N (S n)) = inci (subi i (N n)).
  intros i n.
  rewrite <- ?addi_eq_subinj.
  rewrite ?neg_Nn.
  rewrite addi_i_PSn.
  reflexivity.
  Defined.

Lemma addi_dist_neg_PP : forall (n1 n2 : nat), neg (addi (P n1) (P n2)) = addi (neg (P n1)) (neg (P n2)).
  intros n1 n2.
  rewrite ?neg_Pn.
  induction n1 as [|n1'];
  destruct n2 as [|n2'].
  rewrite <- pz_equals_nz.
  rewrite ?addi_i_O.
  reflexivity.
  rewrite <- pz_equals_nz.
  rewrite ?addi_O_i.
  rewrite ?neg_Pn.
  reflexivity.
  rewrite <- pz_equals_nz.
  rewrite ?addi_i_O.
  rewrite ?neg_Pn.
  reflexivity.
  rewrite addi_NSn_j.
  rewrite addi_PSn_j.
  rewrite neg_inci_eq_deci_neg.
  rewrite IHn1'.
  reflexivity.
  Defined.

Lemma addi_dist_neg_PN : forall (n1 n2 : nat), neg (addi (P n1) (N n2)) = addi (neg (P n1)) (neg (N n2)).
  intros n1 n2.
  rewrite ?neg_Pn.
  rewrite ?neg_Nn.
  induction n1 as [|n1'];
  destruct n2 as [|n2'].
  reflexivity.
  rewrite <- pz_equals_nz.
  rewrite ?addi_O_i.
  rewrite neg_Nn.
  reflexivity.
  rewrite <- pz_equals_nz.
  rewrite ?addi_i_O.
  rewrite neg_Pn.
  reflexivity.
  rewrite addi_PSn_j.
  rewrite addi_NSn_j.
  rewrite neg_inci_eq_deci_neg.
  rewrite IHn1'.
  reflexivity.
  Defined.

Lemma addi_dist_neg_NP : forall (n1 n2 : nat), neg (addi (N n1) (P n2)) = addi (neg (N n1)) (neg (P n2)).
  intros n1 n2.
  rewrite ?neg_Pn.
  rewrite ?neg_Nn.
  induction n1 as [|n1'];
  destruct n2 as [|n2'].
  rewrite <- pz_equals_nz.
  reflexivity.
  rewrite <- pz_equals_nz.
  rewrite ?addi_O_i.
  rewrite neg_Pn.
  reflexivity.
  rewrite <- pz_equals_nz.
  rewrite ?addi_i_O.
  rewrite neg_Nn.
  reflexivity.
  rewrite addi_PSn_j.
  rewrite addi_NSn_j.
  rewrite neg_deci_eq_inci_neg.
  rewrite IHn1'.
  reflexivity.
  Defined.

Lemma addi_dist_neg_NN : forall (n1 n2 : nat), neg (addi (N n1) (N n2)) = addi (neg (N n1)) (neg (N n2)).
  intros n1 n2.
  rewrite ?neg_Pn.
  rewrite ?neg_Nn.
  induction n1 as [|n1'];
  destruct n2 as [|n2'].
  rewrite <- pz_equals_nz.
  reflexivity.
  rewrite <- pz_equals_nz.
  rewrite ?addi_O_i.
  rewrite neg_Nn.
  reflexivity.
  rewrite <- pz_equals_nz.
  rewrite ?addi_i_O.
  rewrite neg_Nn.
  reflexivity.
  rewrite addi_PSn_j.
  rewrite addi_NSn_j.
  rewrite neg_deci_eq_inci_neg.
  rewrite IHn1'.
  reflexivity.
  Defined.

Theorem addi_dist_neg : forall (i j : int), neg (addi i j) = addi (neg i) (neg j).
  destruct i as [n1|n1]; 
  destruct j as [n2|n2].
  rewrite addi_dist_neg_PP; reflexivity.
  rewrite addi_dist_neg_PN; reflexivity.
  rewrite addi_dist_neg_NP; reflexivity.
  rewrite addi_dist_neg_NN; reflexivity.
  Defined.

Lemma neg_neg_eq_i : forall (i : int), neg (neg i) = i.
  destruct i;
  rewrite ?neg_Pn;
  rewrite ?neg_Nn;
  rewrite ?neg_Pn;
  reflexivity.
  Defined.

Theorem subi_anticomm : forall i1 i2 : int, subi i1 i2 = neg (subi i2 i1).
  intros i1 i2.
  rewrite <- ?addi_eq_subinj.
  rewrite (addi_comm i2 (neg i1)).
  rewrite addi_dist_neg.
  rewrite neg_neg_eq_i.
  reflexivity.
  Defined.

Theorem subi_dist_neg : forall (i j : int), neg (subi i j) = subi (neg i) (neg j).
  intros i1 i2.
  rewrite <- ?addi_eq_subinj.
  rewrite addi_dist_neg.
  rewrite ?neg_neg_eq_i.
  reflexivity.
  Defined.

Theorem subi_dist_addiPPP : forall (n m o :  nat), subi (addi (P n) (P m)) (addi (P n) (P o)) = subi (P m) (P o).
  induction n; destruct m; destruct o;
  try rewrite ?addi_i_O;
  try rewrite ?addi_O_i;
  try rewrite ?subi_i_i;
  try reflexivity.
  

Theorem subi_dist_addi : forall (i j k : int), subi (addi i j) (addi i k) = subi j k.
  destruct i; destruct j; destruct k;


Fixpoint muli (i1 i2 : int) := 
  match i1, i2 with
  | P n1, P n2 => P (muln n1 n2)
  | P n1, N n2 => N (muln n1 n2)
  | N n1, P n2 => N (muln n1 n2)
  | N n1, N n2 => P (muln n1 n2)
  end.

Theorem muli_comm : forall (i j : int), muli i j = muli j i.
  destruct i as [n1|n1];
  destruct j as [n2|n2];
  unfold muli;
  try (rewrite muln_comm);
  reflexivity.
  Defined.

Theorem muli_assoc : forall (i j k : int), muli (muli i j) k = muli i (muli j k).
  destruct i as [n1|n1];
  destruct j as [n2|n2];
  destruct k as [n3|n3];
  unfold muli;
  try (rewrite muln_assoc);
  try reflexivity.
  Defined.

Theorem muliPP_eq_muln : forall (n m : nat), muli (P n) (P m) = P (muln n m).
  intros n m.
  reflexivity.
  Defined.

Theorem muliNN_eq_Pmuln : forall (n m : nat), muli (N n) (N m) = P (muln n m).
  intros n m.
  reflexivity.
  Defined.

Theorem muliPN_eq_Nmuln : forall (n m : nat), muli (P n) (N m) = N (muln n m).
  intros n m.
  reflexivity.
  Defined.

Theorem muliNP_eq_Nmuln : forall (n m : nat), muli (N n) (P m) = N (muln n m).
  intros n m.
  reflexivity.
  Defined.

Theorem muli_negi_j : forall (i j : int), muli (neg i) j = neg (muli i j).
  destruct i as [n1|n1];
  destruct j as [n2|n2];
  rewrite ?neg_Pn;
  rewrite ?neg_Nn;
  unfold muli;
  rewrite ?neg_Pn;
  rewrite ?neg_Nn;
  reflexivity.
  Defined.

Theorem muli_i_negj : forall (i j : int), muli i (neg j) = neg (muli i j).
  destruct i as [n1|n1];
  destruct j as [n2|n2];
  rewrite ?neg_Pn;
  rewrite ?neg_Nn;
  unfold muli;
  rewrite ?neg_Pn;
  rewrite ?neg_Nn;
  reflexivity.
  Defined.

Theorem muli_O_i : forall (i : int), muli (P O) i = P O.
  destruct i;
  simpl.
  reflexivity.
  rewrite pz_equals_nz;
  reflexivity.
  Defined.

Theorem muli_i_O : forall (i : int), muli i (P O) = P O.
  destruct i; simpl; rewrite muln_n_O.
  reflexivity.
  rewrite pz_equals_nz.
  reflexivity.
  Defined.

Theorem eq_Pi_n : forall (n m : nat), n = m -> P n = P m. 
  intros n m H.
  rewrite H.
  reflexivity.
  Defined.

Theorem muli_dist_addi_PPP : forall (n1 n2 n3 : nat), muli (P n1) (addi (P n2) (P n3)) = addi (muli (P n1) (P n2)) (muli (P n1) (P n3)).
  destruct n1; destruct n2; destruct n3;
  try (rewrite -> ?muli_O_i; rewrite? addi_O_i; reflexivity);
  try (rewrite -> ?muli_i_O; rewrite? addi_O_i; reflexivity).
  rewrite -> ?muli_i_O. rewrite -> ?addi_i_O; reflexivity.
  assert (forall (a b : nat), addi (P a) (P b) = P (addn a b)).
  simpl. intros a b. rewrite subPN_eq_Padd. reflexivity.
  rewrite -> ?muliPP_eq_muln.
  rewrite <- ?pos_add_ntoi.
  rewrite -> ?muliPP_eq_muln.
  rewrite -> muln_dist_addn.
  reflexivity.  
  Defined.

Theorem muli_dist_addi_PPN : forall (n1 n2 n3 : nat), muli (P n1) (addi (P n2) (N n3)) = addi (muli (P n1) (P n2)) (muli (P n1) (N n3)).
  induction n1; destruct n2; destruct n3;
  try (rewrite -> ?muli_O_i; rewrite? addi_O_i; reflexivity);
  try (rewrite -> ?muli_i_O; rewrite? addi_O_i; reflexivity).
  rewrite <- ?pz_equals_nz. rewrite ?addi_i_O. rewrite ?muli_i_O.
  rewrite ?addi_i_O. reflexivity.
  rewrite ?muliPN_eq_Nmuln.
  rewrite ?muliPP_eq_muln.
  rewrite ?muln_n_Sm.
  rewrite ?muln_Sn_m.
  rewrite ?addn_Sn_m.
  unfold addi. fold addi.
  unfold sub_PPn. fold sub_PPn.

Theorem muli_dist_addi : forall (i j k : int), muli i (addi j k) = addi (muli i j) (muli i k).
  destruct i as [n1|n1];
  destruct j as [n2|n2];
  destruct k as [n3|n3].