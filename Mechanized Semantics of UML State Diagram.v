Require Export String.
Require Import ListSet.
Require Import List.
Require Import Arith.
Require Import Bool.
Open Scope nat_scope.
Open Scope type_scope.
Open Scope string_scope.
Open Scope list_scope.


Definition event:=string.
Definition state:=string.
Definition tname:=string.
Definition action:=list event.
Inductive history : Type :=
|none : history
|deep : history
|shallow : history.
Definition trans := tname*state*set state*event*action*set state*state*history.
Definition label := event * action * bool.
Definition entryexit := action * action.
Definition trace := list event.

Definition event_dec:forall (a b:event) ,{a = b} + {a <> b}.
   exact string_dec.
Defined.

Definition state_dec:forall (a b:state) ,{a = b} + {a <> b}.
   exact string_dec.
Defined.

Definition name_dec:forall (a b:tname) ,{a = b} + {a <> b}.
    repeat decide equality. 
Defined.

Definition action_dec:forall (a b:action) ,{a = b} + {a <> b}.
    repeat decide equality. 
Defined.

Definition trans_dec:forall (a b:trans) ,{a = b} + {a <> b}.
    repeat decide equality. 
Defined.

Definition set_state_dec:forall (a b:set state) ,{a = b} + {a <> b}.
    repeat decide equality. 
Defined.

Inductive sa : Type:=
|base_sa : state -> entryexit -> sa
|or_sa : state -> list sa -> nat -> list trans -> entryexit -> sa
|and_sa : state -> list sa -> entryexit -> sa
.

Definition sa_dec:forall (a1 b1 : sa) ,{a1 = b1} + {a1 <> b1}.
fix 1.
repeat decide equality.
Defined.

Fixpoint conf (p : sa){struct p}: (set state) :=
match p with
|base_sa n ee => (n::nil)
|or_sa n lp l lt ee => set_add state_dec n ( (fix aux (num: nat)(ls: list sa){struct ls}: (set state) :=
    match num,ls with
        | 0, x::l' => conf x
        | S m , x::l' => aux m l'
        | 0, nil => nil
        | S m, nil => "wrong"::nil
    end) l lp)

|and_sa n lp ee=> set_add state_dec n ( (fix aux (l: list sa): (set state) :=
    match l with
        | nil => nil
        | p :: tail => set_union state_dec (conf p) (aux tail)
    end) lp)
end.



Fixpoint getEntry (s:sa) : action :=
match s with
|base_sa n ee => fst ee
|or_sa n lp l lt ee => fst ee
|and_sa n lp ee=> fst ee
end.

Fixpoint getExit (s:sa) : action :=
match s with
|base_sa n ee => snd ee
|or_sa n lp l lt ee => snd ee
|and_sa n lp ee=> snd ee
end.


Fixpoint turnflat (ltr:list (list event)): list event :=
match ltr with
|nil => nil
|tr::tail => tr++ (turnflat tail)
end.

Inductive reconstruct : list sa -> list (list event) -> Prop:=
|r1 :forall lp ltr , ( forall s , set_In s lp ->( exists tr', set_In tr' ltr /\ Entry s tr' )) ->
                     (forall tr', set_In tr' ltr -> (exists s, set_In s lp /\ Entry s tr'))  ->
                     reconstruct lp ltr
with Entry :sa -> action -> Prop :=
|base_entry: forall  n ee  ,Entry (base_sa n ee) (fst ee)
|or_entry: forall n lp l lt ee  s tr t, Entry (nth l lp s) tr -> t = (fst ee) ++ tr -> Entry (or_sa n lp l lt ee) t
|and_entry:forall n lp ee  t ltr,reconstruct lp ltr ->
                 t = (fst ee) ++ (turnflat ltr) ->  Entry (and_sa n lp ee) t
.


Inductive reconstruct_exit : list sa -> list (list event) -> Prop:=
|r_exit :forall lp ltr , ( forall s , set_In s lp ->( exists tr', set_In tr' ltr -> Entry s tr' )) ->
                     (forall tr', set_In tr' ltr -> (exists s, set_In s lp -> Entry s tr'))  ->
                     reconstruct_exit lp ltr
with
Exit :sa -> action -> Prop :=
|base_exit: forall  n ee  ,Exit (base_sa n ee) (snd ee)
|or_exit: forall n lp l lt ee  s tr t, Exit (nth l lp s) tr -> t = (snd ee) ++ tr -> Exit (or_sa n lp l lt ee) t
|and_exit:forall n lp ee  t ltr,reconstruct_exit lp ltr ->
                 t = (snd ee) ++ (turnflat ltr) ->  Exit (and_sa n lp ee) t
.



Fixpoint subst_or (p: sa) (sl:sa) (sl':sa){struct p} :  sa :=
match p with 
|or_sa n lp l lt ee  => ( or_sa n ((fix aux (ls: list sa): list sa :=
    match ls with
        | nil => nil
        | s :: tail => if (sa_dec s sl) then sl'::tail else s:: (aux tail)

    end) lp) l lt ee)
|_ => p
end.

Fixpoint subst_and (p: sa) (sl:sa) (sl':sa) :  sa :=
match p with 
|and_sa n lp ee => ( and_sa n ((fix aux (ls: list sa): list sa :=
    match ls with
        | nil => nil
        | s :: tail => if (sa_dec s sl) then sl'::tail else s:: (aux tail)

    end) lp) ee )
|_ => p
end.

Fixpoint default (s : sa): sa :=
match s with
|base_sa n ee => base_sa n ee
|or_sa n nil l lt ee => or_sa n nil 0 lt ee
|or_sa n (sdf::stail) l lt ee => or_sa n ((default sdf)::stail) 0 lt ee
|and_sa n lp ee => and_sa n ( (fix aux (l: list sa): (list sa) :=
    match l with
        | nil => nil
        | p :: tail => (default p) :: aux tail
    end) lp) ee
end.

Fixpoint next_stop_or (h:history)(s:sa):sa :=
match s,h with
|or_sa n lp l lt ee,none => subst_or s (nth 0 lp s) (default (nth 0 lp s))
|or_sa n lp l lt ee,deep =>or_sa n lp l lt ee
|or_sa n lp l lt ee,shallow =>subst_or s (nth l lp s) (default (nth l lp s))
|_,_ => s
end.

Fixpoint pos (s:state)(ln:set state)(n:nat) : option nat :=
match ln with
|nil => None 
|s'::tail => if state_dec s s' then Some n else pos s tail (S n)
end.

Fixpoint sa_pos (s:sa)(lp:set sa)(n:nat) : option nat :=
match lp with
|nil => None 
|s'::tail => if sa_dec s s' then Some n else sa_pos s tail (S n)
end.

Fixpoint next (h:history)(ln:set state)(s:sa){struct s} :sa :=
match s with
|base_sa n ee => base_sa n ee
|or_sa n lp l lt ee => match (pos n ln 0) with
                       |None => next_stop_or h s
                       |Some j => ( or_sa n ((fix aux (ls: list sa): list sa :=
                                 match ls with
                                 | nil => nil
                                 | s' :: tail => if (sa_dec s' (nth j lp s')) then (next h ln s')::tail else s':: (aux tail)
                                 end) lp) j lt ee)
                       end                
         
|and_sa n lp ee => and_sa n ( (fix aux (l: list sa){struct l}: (list sa) :=
    match l with
        | nil => nil
        | p :: tail => (next h ln p) :: aux tail
    end) lp)  ee
end.


Fixpoint getState (s: sa) : state :=
match s with 
|base_sa n ee => n
|or_sa n lp l lt ee => n
|and_sa n lp ee=> n
end.

(*------Priority proposition --------*)
Inductive p : event -> sa -> Prop :=
|p_or: forall l lp (lt:list trans) n tn i s e a ee sr td h,set_In (tn,(getState (nth l lp s)),sr,e,a,td,(getState (nth i lp s)),h) lt  
  -> (forall st, set_In st sr -> set_In st (conf (nth l lp s)))
  -> p e (or_sa n lp l lt ee)
|p_and:forall n lp e ee, (exists s, set_In  s lp -> p e s) -> p e (and_sa n lp ee) .

Inductive subst_and_r : list sa -> sa -> sa ->list sa -> Prop :=
|r_subst: forall lp lp' sj sj' n ee pos, sa_pos sj lp 0 = Some pos -> (nth pos lp' (base_sa n ee)) =sj' ->
                     subst_and_r lp sj sj' lp'
.



(*-----operational semantic-------*)
Inductive reconstruct_action :event -> list sa -> list (list event) ->list sa -> bool -> Prop:=
|r_action_true :forall lp ltr lp' e, (exists sj, exists a,exists sj',  set_In sj lp /\sred sj (e,a,true) sj') ->
                     ( forall sj sj', set_In sj lp ->  subst_and_r lp sj sj' lp' ->
                     ( exists tr',exists f, set_In tr' ltr  /\ sred sj (e,tr',f) sj') ) ->
                     (forall tr' sj', set_In tr' ltr -> (exists sj,exists f, subst_and_r lp sj sj' lp' ->  set_In sj lp /\ sred sj (e,tr',f) sj'))  ->
                     reconstruct_action e lp ltr lp' true
|r_action_false :forall lp ltr  e, ( forall sj, set_In sj lp -> sred sj (e,nil,false) sj) ->
                     reconstruct_action e lp ltr lp false
with
 sred: sa -> label -> sa -> Prop :=
|BAS: forall  e n ee, sred (base_sa n ee) (e,nil,false) (base_sa n ee) 
|OR1: forall  e a n lp l lt i tn s ee en ex tr sr td h s', set_In (tn,(getState (nth l lp s)),sr,e,a,td,(getState (nth i lp s)),h) lt 
    -> (forall st, set_In st sr -> set_In st (conf (nth l lp s)))
    -> ~p e (nth l lp s)
    -> Exit (nth l lp s) ex  ->Entry (nth i lp s) en  -> tr = ex ++ a ++ en
    -> s' = subst_or (or_sa n lp i lt ee) (nth i lp s) (next h td (nth i lp s))
    ->sred (or_sa n lp l lt ee) (e,tr,true) s'
|OR2: forall sl sl' e l' lp' lt' n' l lp n lt tr ee, sred sl (e,tr,true) sl' -> nth l lp sl = sl
 -> nth l' lp' sl' = sl' -> or_sa n' lp' l' lt' ee = subst_or (or_sa n lp l lt ee) sl sl' 
 -> sred (or_sa n lp l lt ee) (e,tr,true) (or_sa n' lp' l' lt' ee)
|OR3: forall sl e n lp l t ee, sred sl (e,nil,false) sl   -> sl = nth l lp sl  -> ~p e (or_sa n lp l t ee) ->
      sred (or_sa n lp l t ee) (e,nil,false) (or_sa n lp l t ee) 
|AND: forall   e f lp n ee  tr' tr lp',   
       reconstruct_action e lp tr' lp' f -> tr = turnflat tr' ->
       sred  (and_sa n lp ee) (e,tr,f) (and_sa n lp' ee)    
.


Inductive sstar:sa -> trace -> sa -> trace -> Prop:=
|sstar_self: forall s t, sstar s t s t
|sstar_trans: forall s t s' t' s'' t'' a b  e,sstar s t s' t' -> sred s' (hd e t',a,b) s'' -> 
        t'' = (tl t') ++ a -> sstar s t s'' t''.




(*------Example------*)
Definition SALwait : sa := base_sa "Lwait" (nil,nil).
Definition SALwrite : sa := base_sa "Lwrite" (nil,nil).
Definition SASid : sa := base_sa "Sid" (nil,nil).
Definition SASpwd : sa := base_sa "Spwd" (nil,nil).
Definition SAScmd : sa := base_sa "Scmd" ("encmd"::nil,nil).


Definition t1: trans :=("t1","Sid",nil,"eid",nil,nil,"Spwd",none).
Definition t2: trans :=("t2","Scmd",nil,"ecmd",nil,nil,"Sident",shallow).
Definition t3: trans :=("t3","Sident",nil,"eid","eerror"::nil,nil,"Scmd",none).
Definition t4: trans :=("t4","Sident",("Spwd"::nil),"epwd","eloginsucc"::nil,nil,"Scmd",none).
Definition t5: trans :=("t5","Lwait",nil,"eid",nil,nil,"Lwrite",none).


Definition SASident : sa := or_sa "Sident" (SASid::SASpwd::nil) 0 (t1::nil) (nil,"exlogin"::nil).
Definition SASLog : sa := or_sa "SLog" (SALwait::SALwrite::nil) 0 (t5::nil) (nil,nil).
Definition SASexecute : sa := or_sa "Sexecute" (SASident::SAScmd::nil) 0 (t2::t3::t4::nil) (nil,nil).
Definition SASserver : sa := and_sa "Sserver" (SASexecute::SASLog::nil) (nil,nil).

Definition SASident1 : sa := or_sa "Sident" (SASid::SASpwd::nil) 1 (t1::nil) (nil,"exlogin"::nil).
Definition SASexecute1 : sa := or_sa "Sexecute" (SASident1::SAScmd::nil) 0 (t2::t3::t4::nil) (nil,nil).
Definition SASLog1 : sa := or_sa "SLog" (SALwait::SALwrite::nil) 1 (t5::nil) (nil,nil).
Definition SASserver1 : sa := and_sa "Sserver" (SASexecute1::SASLog1::nil) (nil,nil).
Definition SASexecute2 : sa := or_sa "Sexecute" (SASident1::SAScmd::nil) 1 (t2::t3::t4::nil) (nil,nil).
Definition SASserver2 : sa := and_sa "Sserver" (SASexecute2::SASLog1::nil) (nil,nil).

 Example examplfalse: ~ sred SASserver ("eid","eerror"::nil,true)  SASserver2.
Proof.
 intuition.
 inversion H. subst. clear H.
 inversion H2; subst. clear H2. clear H. clear H1. clear H8.
 destruct H0 with (sj:=SASexecute)(sj':=SASexecute2).
 simpl;auto.
 apply r_subst with (n:="err")(ee:=(nil,nil))(pos:=0). 
 simpl. auto.
 simpl. auto.
 clear H0.
 destruct H. destruct H.
 inversion H0;clear H0. subst. 
 simpl in H12. 
 apply H12.
 apply p_or with (tn:="t1")(i:=1)(s:=SASident)(a:=nil)(sr:=nil)(td:=nil)(h:=none).
 simpl; auto.
 intros st Hfalse.
 inversion Hfalse.
 simpl in H14. simpl in H15. subst. 
 inversion H16.
Qed.



Example examp :sstar SASserver ("eid"::"epwd"::"ecmd"::nil) SASserver1 nil.
Proof.
 apply sstar_trans with (s':= SASserver1) (t':="encmd"::nil)(e:="encmd")(a:=nil)(b:=false).
 apply sstar_trans with (s':= SASserver1) (t':="eloginsucc"::"encmd"::nil)(e:="eloginsucc")(a:=nil)(b:=false).
 apply sstar_trans with (s':= SASserver1) (t':="exlogin"::"eloginsucc"::"encmd"::nil)(e:="exlogin")(a:=nil)(b:=false).
 apply sstar_trans with (s':= SASserver2) (t':="ecmd"::"exlogin"::"eloginsucc"::"encmd"::nil)(e:="ecmd")(a:=nil)(b:=true).
 apply sstar_trans with (s':= SASserver1) (t':="epwd"::"ecmd"::nil)(e:="epwd")(a:="exlogin"::"eloginsucc"::"encmd"::nil)(b:=true).
 apply sstar_trans with (s':= SASserver) (t':="eid"::"epwd"::"ecmd"::nil)(e:="eid")(a:=nil)(b:=true).
 apply sstar_self.

(*Sserver -> Sserver1 /eid*)
 apply AND with (tr':=nil::nil).
 apply r_action_true.
     (*true flag*)
    exists SASexecute. exists nil. exists SASexecute1. 
    split;simpl;auto.
     (* sred SASexecute ("eid", nil, true) SASexecute1 *)
     apply OR2 with (sl:=SASident)(sl':=SASident1) .
     apply OR1 with (a:=nil)(i:=1)(tn:="t1")(s:=SASident)(en:=nil)(ex:=nil)(sr:=nil)(td:=nil)(h:=none).
     simpl. auto.
     intros st H. inversion H.
     intuition. inversion H.
     constructor. constructor.
     simpl;auto.
     simpl;auto.
     simpl;auto.
     simpl;auto.
     simpl;auto.
    (*->*)
      intros sj sj' HsetIn Hsubst.
      inversion HsetIn;clear HsetIn;subst.
        (*SASexecute*)
        inversion Hsubst;clear Hsubst;subst.
        inversion H;clear H;subst.
        exists nil. exists true. 
        split; simpl;auto.
          (* sred SASexecute ("eid", nil, true) SASexecute1 *)
          apply OR2 with (sl:=SASident)(sl':=SASident1) .
          apply OR1 with (a:=nil)(i:=1)(tn:="t1")(s:=SASident)(en:=nil)(ex:=nil)(sr:=nil)(td:=nil)(h:=none).
          simpl. auto.
          intros st H. inversion H.
          intuition. inversion H.
          constructor. constructor.
          simpl;auto.
          simpl;auto.
          simpl;auto.
          simpl;auto.
          simpl;auto.
       (*SASLog*)
       inversion Hsubst;clear Hsubst;subst. destruct H. subst.
       inversion H0;clear H0;subst.
       exists nil. exists true. 
       split; simpl;auto.
          (* sred SASLog ("eid", nil, false) SASLog1*)
          apply OR1 with (a:=nil)(i:=1)(tn:="t5")(s:=SASident)(en:=nil)(ex:=nil)(sr:=nil)(td:=nil)(h:=none).
          simpl. auto.
          intros st H. inversion H.
          intuition. inversion H.
          constructor. constructor.
          simpl;auto.
          simpl;auto.
       (*False*)
       inversion H.
     (*<-*)
     intros tr' sj' HsetIn.
     inversion HsetIn;clear HsetIn;subst.
       (*nil*)
        exists SAScmd.  exists true. 
        split;inversion H;clear H;subst;inversion H0.
       (*False*)
        inversion H.
  simpl. auto.
  (*--*)
  simpl;auto.

(*Sserver1 -> Sserver2 /epwd*)
 apply AND with (tr':=("exlogin"::"eloginsucc"::"encmd"::nil)::nil::nil).
(* AND *)
    apply r_action_true.
     (*true flag*)
    exists SASexecute1. exists ("exlogin"::"eloginsucc"::"encmd"::nil). exists SASexecute2. 
    split;simpl;auto.
     (* sred SASexecute1 ("epwd", "eloginsucc" :: nil, true) SASexecute2 *)
     apply OR1 with (a:="eloginsucc"::nil)(i:=1)(tn:="t4")(s:=SASident)(en:="encmd"::nil)(ex:="exlogin"::nil)(sr:="Spwd"::nil)(td:=nil)(h:=none).
     simpl. auto.
     intros st H. inversion H;clear H;subst. simpl;auto. inversion H0.
     (*~p*)
     intuition. inversion H;clear H;subst. destruct H3; inversion H.
     (*exit action*)
     apply or_exit with (s:=SAScmd)(tr:=nil). constructor. simpl;auto.
     (*entry action*) 
     constructor. simpl;auto.
     simpl;auto.
    (*->*)
      intros sj sj' HsetIn Hsubst.
      inversion HsetIn;clear HsetIn;subst.
        (*SASexecute1*)
        inversion Hsubst;clear Hsubst;subst.
        inversion H;clear H;subst.
        exists ("exlogin"::"eloginsucc"::"encmd"::nil). exists true. 
        split; simpl;auto.
           (* sred SASexecute1 ("epwd", "eloginsucc" :: nil, true) SASexecute2 *)
           apply OR1 with (a:="eloginsucc"::nil)(i:=1)(tn:="t4")(s:=SASident)(en:="encmd"::nil)(ex:="exlogin"::nil)(sr:="Spwd"::nil)(td:=nil)(h:=none).
           simpl. auto.
           intros st H. inversion H;clear H;subst. simpl;auto. inversion H0.
           (*~p*)
           intuition. inversion H;clear H;subst. destruct H3; inversion H.
           (*exit action*)
           apply or_exit with (s:=SAScmd)(tr:=nil). constructor. simpl;auto.
           (*entry action*) 
           constructor. simpl;auto.
           simpl;auto.
       (*SASLog1*)
       inversion Hsubst;clear Hsubst;subst. destruct H. subst.
       inversion H0;clear H0;subst.
       exists nil. exists false. 
       split; simpl;auto.
         apply OR3 with (sl:=SALwrite).
         apply BAS.
         simpl;auto.
         (*~p*)
         intuition. inversion H;clear H;subst.
         destruct H3. inversion H.
         inversion H.
       (*False*)
       inversion H.
     (*<-*)
     intros tr' sj' HsetIn.
     inversion HsetIn;clear HsetIn;subst.
       (*"exlogin" :: "eloginsucc" :: "encmd" :: nil*)
        exists SASexecute1. exists true.
        split; simpl;auto. 
        inversion H;clear H;subst.
        inversion H0;clear H0;subst.
          (* sred SASexecute1 ("epwd", "exlogin" :: "eloginsucc" :: "encmd" :: nil, true) SASexecute2 *)
           apply OR1 with (a:="eloginsucc"::nil)(i:=1)(tn:="t4")(s:=SASident)(en:="encmd"::nil)(ex:="exlogin"::nil)(sr:="Spwd"::nil)(td:=nil)(h:=none).
           simpl. auto.
           intros st H. inversion H;clear H;subst. simpl;auto. inversion H0.
           (*~p*)
           intuition. inversion H;clear H;subst. destruct H3; inversion H.
           (*exit action*)
           apply or_exit with (s:=SAScmd)(tr:=nil). constructor. simpl;auto.
           (*entry action*) 
           constructor. simpl;auto.
           simpl;auto.
       (*nil*)
        destruct H;subst.
        exists SASLog.  exists false. 
        split;inversion H;clear H;subst;inversion H0.
       (*False*)
        inversion H.
simpl;auto.
(*--*)
 simpl;auto.

(*Sserver2 -> Sserver1 /ecmd*)
 apply AND with (tr':=nil::nil).
  (* AND *)
    apply r_action_true.
     (*true flag*)
    exists SASexecute2. exists nil. exists SASexecute1. 
    split;simpl;auto.
     (* sred SASexecute2 ("ecmd", nil, true) SASexecute1 *)
     apply OR1 with (a:=nil)(i:=0)(tn:="t2")(s:=SASident)(en:=nil)(ex:=nil)(sr:=nil)(td:=nil)(h:=shallow).
     simpl. auto.
     intros st H. inversion H.
     intuition. inversion H.
     constructor. simpl. apply or_entry with (s:=SASident1)(tr:=nil).  constructor.
     simpl;auto.
     simpl;auto.
     simpl;auto.
    (*->*)
      intros sj sj' HsetIn Hsubst.
      inversion HsetIn;clear HsetIn;subst.
        (*SASexecute2*)
        inversion Hsubst;clear Hsubst;subst.
        inversion H;clear H;subst.
        exists nil. exists true. 
        split; simpl;auto.
          (* sred SASexecute2 ("ecmd", nil, true) SASexecute1 *)
          apply OR1 with (a:=nil)(i:=0)(tn:="t2")(s:=SASident)(en:=nil)(ex:=nil)(sr:=nil)(td:=nil)(h:=shallow).
          simpl. auto.
          intros st H. inversion H.
          intuition. inversion H.
          constructor. simpl. apply or_entry with (s:=SASident1)(tr:=nil).  constructor.
          simpl;auto.
          simpl;auto.
          simpl;auto.
       (*SASLog1*)
       inversion Hsubst;clear Hsubst;subst. destruct H. subst.
       inversion H0;clear H0;subst.
       exists nil. exists false. 
       split; simpl;auto.
         apply OR3 with (sl:=SALwrite).
         apply BAS.
         simpl;auto.
         (*~p*)
         intuition. inversion H;clear H;subst.
         destruct H3. inversion H.
         inversion H.
       (*False*)
       inversion H.
     (*<-*)
     intros tr' sj' HsetIn.
     inversion HsetIn;clear HsetIn;subst.
       (*nil*)
        exists SAScmd.  exists true. 
        split;inversion H;clear H;subst;inversion H0.
       (*False*)
        inversion H.
  (*--*)
  simpl. auto.

(**)
  simpl. auto.

(*Sserver1 /exlogin*)
apply AND with (tr':=nil::nil).
  apply r_action_false.
  intros sj HsetIn.
  inversion HsetIn;clear HsetIn;subst.
  (*Sexecute1*)
  apply OR3 with (sl:=SASident1).
  apply OR3 with (sl:=SASpwd).
  apply BAS.
  simpl;auto.
  intuition. inversion H;clear H;subst. destruct H3;inversion H.
  simpl;auto.
  intuition. inversion H;clear H;subst. destruct H3. inversion H.
  destruct H. inversion H. destruct H;inversion H.
  destruct H. subst.
 (*SASLog1*)
  apply OR3 with (sl:=SALwrite).
  apply BAS.
  simpl;auto.
  intuition. inversion H;clear H;subst. destruct H3;inversion H.
  inversion H.
  simpl;auto.
  simpl;auto.

(*Sserver1 /eloginsucc*)
apply AND with (tr':=nil::nil).
  apply r_action_false.
  intros sj HsetIn.
  inversion HsetIn;clear HsetIn;subst.
  (*Sexecute1*)
  apply OR3 with (sl:=SASident1).
  apply OR3 with (sl:=SASpwd).
  apply BAS.
  simpl;auto.
  intuition. inversion H;clear H;subst. destruct H3;inversion H.
  simpl;auto.
  intuition. inversion H;clear H;subst. destruct H3. inversion H.
  destruct H. inversion H. destruct H;inversion H.
  destruct H. subst.
 (*SASLog1*)
  apply OR3 with (sl:=SALwrite).
  apply BAS.
  simpl;auto.
  intuition. inversion H;clear H;subst. destruct H3;inversion H.
  inversion H.
  simpl;auto.
  simpl;auto.

(*Sserver1 /encmd*)
apply AND with (tr':=nil::nil).
  apply r_action_false.
  intros sj HsetIn.
  inversion HsetIn;clear HsetIn;subst.
  (*Sexecute1*)
  apply OR3 with (sl:=SASident1).
  apply OR3 with (sl:=SASpwd).
  apply BAS.
  simpl;auto.
  intuition. inversion H;clear H;subst. destruct H3;inversion H.
  simpl;auto.
  intuition. inversion H;clear H;subst. destruct H3. inversion H.
  destruct H. inversion H. destruct H;inversion H.
  destruct H. subst.
 (*SASLog1*)
  apply OR3 with (sl:=SALwrite).
  apply BAS.
  simpl;auto.
  intuition. inversion H;clear H;subst. destruct H3;inversion H.
  inversion H.
  simpl;auto.
  simpl;auto.
Qed.

