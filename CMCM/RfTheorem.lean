import CMCM.Rf

variable {n : ℕ}

/-
Intervening writes:
for all writes `e_w_inter` in the behaviour (that are not `e_w`):
- GLE `e_w_inter` is not between `e_w`'s GLE and `e_r`'s GLE
- if CLE `e_w` and CLE `e_r` are in the same cluster, then CLE `e_w_inter` is not between CLE `e_w` and CLE `e_r`
-/

def NotBetweenGLEs (e_inter_gle e_w_gle e_r_gle : Event n)
  /-
  (e_inter e_w e_r : Event n)
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  {hinter_cluster : e_inter.isClusterCache}
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  (hinter_is_write : e_inter.isWrite)
  (hw_is_write : e_w.isWrite) (r_is_read : e_r.isRead)
  {hinter_not_down : ¬ e_inter.down}
  {hw_not_down : ¬ e_w.down} {r_not_down : ¬ e_r.down}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster hw_not_down)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster r_not_down)
  (hinter_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_inter hinter_cluster hinter_not_down)
  -/
  : Prop := ¬ e_inter_gle.OrderedBetween n e_w_gle e_r_gle

def SameClusterCLE.NotBetweenCLEs (e_inter_cle e_w_cle e_r_cle : Event n) : Prop :=
  e_inter_cle.protocol = e_w_cle.protocol ∧ e_inter_cle.protocol = e_r_cle.protocol →
  ¬ e_inter_cle.OrderedBetween n e_w_cle e_r_cle

structure NoInterveningWrites.constraints
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  (hw_is_write : e_w.isWrite) (r_is_read : e_r.isRead)
  {hw_not_down : ¬ e_w.down} {r_not_down : ¬ e_r.down}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster hw_not_down)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster r_not_down)
  (e_w_inter : Event n)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  : Prop where
  interWrite : e_w_inter.isWrite
  notDown : ¬ e_w_inter.down
  clusterW : e_w_inter.isClusterCache
  notSameAsW : e_w_inter ≠ e_w
  notBetweenGles :
    NotBetweenGLEs
      (hknow_dir_access cmp b init e_w_inter clusterW notDown).hreq's_global_lin.choose
      hw_c_and_g_lin.hreq's_global_lin.choose
      hr_c_and_g_lin.hreq's_global_lin.choose
  notBetweenCles :
    SameClusterCLE.NotBetweenCLEs
      (hknow_dir_access cmp b init e_w_inter clusterW notDown).hreq's_global_lin.choose
      hw_c_and_g_lin.hreq's_global_lin.choose
      hr_c_and_g_lin.hreq's_global_lin.choose

def NoInterveningWrites
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  (hw_is_write : e_w.isWrite) (r_is_read : e_r.isRead)
  {hw_not_down : ¬ e_w.down} {r_not_down : ¬ e_r.down}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster hw_not_down)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster r_not_down)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
  : Prop :=
  ∀ e_w_inter ∈ b,
    NoInterveningWrites.constraints hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin e_w_inter hknow_dir_access

theorem CMCM.rf_holds
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  (hw_is_write : e_w.isWrite) (r_is_read : e_r.isRead)
  {hw_not_down : ¬ e_w.down} {r_not_down : ¬ e_r.down}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster hw_not_down)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster r_not_down)
  -- Synchronization conditions.
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hno_intervening_writes : NoInterveningWrites hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
  : Behaviour.readsFrom.cases hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin
  := by
  -- probably want to start with cases of `e_w` and `e_r`'s GLEs.
  -- Only expand cases of `e_w` and `e_r`'s requests (coherent, non-coherent, release, acquire...) further into the subcases.
  sorry
