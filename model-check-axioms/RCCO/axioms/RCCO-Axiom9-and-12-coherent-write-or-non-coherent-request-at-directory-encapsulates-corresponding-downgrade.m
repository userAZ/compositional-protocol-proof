/*
  Copyright (c) 2021.  Nicolai Oswald
  Copyright (c) 2021.  University of Edinburgh
  All rights reserved.

  Redistribution and use in source and binary forms, with or without
  modification, are permitted provided that the following conditions are
  met: redistributions of source code must retain the above copyright
  notice, this list of conditions and the following disclaimer;
  redistributions in binary form must reproduce the above copyright
  notice, this list of conditions and the following disclaimer in the
  documentation and/or other materials provided with the distribution;
  neither the name of the copyright holders nor the names of its
  contributors may be used to endorse or promote products derived from
  this software without specific prior written permission.

  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
  OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/
--Backend/Murphi/MurphiModular/Constants/GenConst
  ---- System access constants
  const
    ENABLE_QS: false;
    VAL_COUNT: 1;
    ADR_COUNT: 1;
  
  ---- System network constants
    O_NET_MAX: 12;
    U_NET_MAX: 12;
  
  ---- SSP declaration constants
    NrCachesL1C1: 4;
  
--Backend/Murphi/MurphiModular/GenTypes
  type
    ----Backend/Murphi/MurphiModular/Types/GenAdrDef
    Address: scalarset(ADR_COUNT);
    ClValue: 0..VAL_COUNT;
    
    ----Backend/Murphi/MurphiModular/Types/Enums/GenEnums
      ------Backend/Murphi/MurphiModular/Types/Enums/SubEnums/GenAccess
      PermissionType: enum {
        load, 
        store, 
        evict, 
        acquire, 
        release, 
        none
      };
      
      ------Backend/Murphi/MurphiModular/Types/Enums/SubEnums/GenMessageTypes
      MessageType: enum {
        GetVL1C1, 
        GetOL1C1, 
        PutOL1C1, 
        WB_AckL1C1, 
        GetV_AckL1C1, 
        GetO_AckL1C1, 
        PutO_AckL1C1, 
        Fwd_GetOL1C1
      };
      
      ------Backend/Murphi/MurphiModular/Types/Enums/SubEnums/GenArchEnums
      s_cacheL1C1: enum {
        cacheL1C1_V_store,
        cacheL1C1_V_release,
        cacheL1C1_V_acquire_GetV_Ack,
        cacheL1C1_V_acquire,
        cacheL1C1_V,
        cacheL1C1_O_evict_x_V,
        cacheL1C1_O_evict,
        cacheL1C1_O,
        cacheL1C1_I_store,
        cacheL1C1_I_release,
        cacheL1C1_I_load,
        cacheL1C1_I_acquire_GetV_Ack,
        cacheL1C1_I_acquire,
        cacheL1C1_I
      };
      
      e_cacheL1C1: enum {
        cacheL1C1_acq_eventL1C1
      };
      
      s_directoryL1C1: enum {
        -- [Shim state translations]
        directoryL1C1_I_to_O_shim_transient,
        directoryL1C1_I_to_V_shim_transient,
        directoryL1C1_V_to_O_shim_transient,
        directoryL1C1_I_to_O_shim_complete,
        directoryL1C1_I_to_V_shim_complete,
        directoryL1C1_V_to_O_shim_complete,
        -- [HeteroGen]
        directoryL1C1_dO_GetO_x_pI_store,
        directoryL1C1_dO_GetO_x_pI_release,
        directoryL1C1_V,
        directoryL1C1_O_GetV,
        directoryL1C1_O_GetO,
        directoryL1C1_O,
        directoryL1C1_I
      };
      
      e_directoryL1C1: enum {
        directoryL1C1_acq_eventL1C1
      };
      
    ----Backend/Murphi/MurphiModular/Types/GenMachineSets
      -- Cluster: C1
      OBJSET_cacheL1C1: scalarset(3);
      OBJSET_directoryL1C1: enum{directoryL1C1};
      C1Machines: union{OBJSET_cacheL1C1, OBJSET_directoryL1C1};
      
      Machines: union{OBJSET_cacheL1C1, OBJSET_directoryL1C1};
    
    ----Backend/Murphi/MurphiModular/Types/GenCheckTypes
      ------Backend/Murphi/MurphiModular/Types/CheckTypes/GenPermType
        acc_type_obj: multiset[3] of PermissionType;
        PermMonitor: array[Machines] of array[Address] of acc_type_obj;
      
    
    ----Backend/Murphi/MurphiModular/Types/GenMessage
      Message: record
        adr: Address;
        mtype: MessageType;
        src: Machines;
        dst: Machines;
        cl: ClValue;
      end;
      
    ----Backend/Murphi/MurphiModular/Types/GenNetwork
      NET_Ordered: array[Machines] of array[0..O_NET_MAX-1] of Message;
      NET_Ordered_cnt: array[Machines] of 0..O_NET_MAX;
      NET_Unordered: array[Machines] of multiset[U_NET_MAX] of Message;
    
    ----Backend/Murphi/MurphiModular/Types/GenMachines
      
      ENTRY_cacheL1C1: record
        State: s_cacheL1C1;
        cl: ClValue;
      end;
      
      EVENT_ENTRY_cacheL1C1: record
          evt_type: e_cacheL1C1;
          evt_adr: Address;
      end;
      
      EVENT_cacheL1C1: record
          event_queue: array[0..ADR_COUNT] of EVENT_ENTRY_cacheL1C1;
          event_queue_index: 0..ADR_COUNT+1;
          pend_adr: multiset[ADR_COUNT+1] of Address;
          event_lock_adr: Address;
      
      end;
      
      MACH_cacheL1C1: record
        cb: array[Address] of ENTRY_cacheL1C1;
        evt: EVENT_cacheL1C1;
      end;
      
      OBJ_cacheL1C1: array[OBJSET_cacheL1C1] of MACH_cacheL1C1;
      
      ENTRY_directoryL1C1: record
        State: s_directoryL1C1;
        cl: ClValue;
        ownerL1C1: Machines;
        -- [Axiom 9/12]
        coherentWriteFlag : boolean;
        previous_ownerL1C1: Machines;
      end;
      
      EVENT_ENTRY_directoryL1C1: record
          evt_type: e_directoryL1C1;
          evt_adr: Address;
      end;
      
      EVENT_directoryL1C1: record
          event_queue: array[0..ADR_COUNT] of EVENT_ENTRY_directoryL1C1;
          event_queue_index: 0..ADR_COUNT+1;
          pend_adr: multiset[ADR_COUNT+1] of Address;
          event_lock_adr: Address;
      
      end;
      
      MACH_directoryL1C1: record
        cb: array[Address] of ENTRY_directoryL1C1;
        evt: EVENT_directoryL1C1;
      end;
      
      OBJ_directoryL1C1: array[OBJSET_directoryL1C1] of MACH_directoryL1C1;
    

  var
    --Backend/Murphi/MurphiModular/GenVars
      fwd: NET_Ordered;
      cnt_fwd: NET_Ordered_cnt;
      resp: NET_Ordered;
      cnt_resp: NET_Ordered_cnt;
      req: NET_Ordered;
      cnt_req: NET_Ordered_cnt;
    
    
      g_perm: PermMonitor;
      i_cacheL1C1: OBJ_cacheL1C1;
      i_directoryL1C1: OBJ_directoryL1C1;
  
--Backend/Murphi/MurphiModular/GenFunctions

  ----Backend/Murphi/MurphiModular/Functions/GenResetFunc
    procedure ResetMachine_cacheL1C1();
    begin
      for i:OBJSET_cacheL1C1 do
        for a:Address do
          i_cacheL1C1[i].cb[a].State := cacheL1C1_I;
          i_cacheL1C1[i].cb[a].cl := 0;
    
        endfor;
      endfor;
    end;
    
    procedure ResetMachine_directoryL1C1();
    begin
      for i:OBJSET_directoryL1C1 do
        for a:Address do
          i_directoryL1C1[i].cb[a].State := directoryL1C1_I;
          i_directoryL1C1[i].cb[a].cl := 0;
          undefine i_directoryL1C1[i].cb[a].ownerL1C1;
    
        endfor;
      endfor;
    end;
    
      procedure ResetMachine_();
      begin
      ResetMachine_cacheL1C1();
      ResetMachine_directoryL1C1();
      
      end;
  ----Backend/Murphi/MurphiModular/Functions/GenEventFunc
    procedure NextEvent_cacheL1C1(m: OBJSET_cacheL1C1);
    begin
      alias evt_entry: i_cacheL1C1[m].evt do
      alias evt_index: evt_entry.event_queue_index do
      alias pend_adr: evt_entry.pend_adr do
    
        if isundefined(evt_entry.event_queue[0].evt_type) then
            return;
        endif;
    
        if MultisetCount(a:pend_adr, true) > 0 then
          return;
        else
          if evt_entry.event_queue_index > 0 then
            for a: Address do
              if a != evt_entry.event_queue[0].evt_adr then
                MultisetAdd(a, pend_adr);
              endif;
            endfor;
          endif;
        endif;
    
      endalias;
      endalias;
      endalias;
    end;
    
    procedure PopEvent_cacheL1C1(m: OBJSET_cacheL1C1);
    begin
      alias evt_entry: i_cacheL1C1[m].evt do
      alias evt_index: evt_entry.event_queue_index do
    
        for i := 0 to evt_index-1 do
          if i < evt_index-1 then
            evt_entry.event_queue[i] := evt_entry.event_queue[i+1];
          else
            undefine evt_entry.event_queue[i];
          endif;
        endfor;
    
        evt_index := evt_index - 1;
    
      endalias;
      endalias;
    end;
    
    procedure ResetEvent_cacheL1C1();
    begin
      for m: OBJSET_cacheL1C1 do
        alias evt_entry: i_cacheL1C1[m].evt do
          undefine evt_entry.event_queue;
          evt_entry.event_queue_index := 0;
          undefine evt_entry.pend_adr;
          undefine evt_entry.event_lock_adr
        endalias;
      endfor;
    end;
    
    procedure IssueEvent_cacheL1C1(evt_type: e_cacheL1C1; m: OBJSET_cacheL1C1; adr: Address);
    begin
      alias evt_entry: i_cacheL1C1[m].evt do
      alias evt_index: evt_entry.event_queue_index do
    
        evt_entry.event_queue[evt_index].evt_type := evt_type;
        evt_entry.event_queue[evt_index].evt_adr := adr;
        evt_index := evt_index + 1;
    
        NextEvent_cacheL1C1(m);
    
      endalias;
      endalias;
    end;
    
    /* Event: Checks if the currently pending event has been served*/
    function CheckRemoteEvent_cacheL1C1(cur_evt_type: e_cacheL1C1; m: OBJSET_cacheL1C1; adr: Address): boolean;
    begin
      alias evt_entry: i_cacheL1C1[m].evt do
      alias pend_adr: i_cacheL1C1[m].evt.pend_adr do
    
        if isundefined(evt_entry.event_queue[0].evt_type) then
            return false;
        endif;
    
        /* Check if the event type matches and the event still need to be served for this address */
        if evt_entry.event_queue[0].evt_type = cur_evt_type & MultisetCount(a: pend_adr, pend_adr[a] = adr) = 1 then
            return true;
        endif;
    
        return false;
    
      endalias;
      endalias;
    end;
    
    procedure ServeRemoteEvent_cacheL1C1(cur_evt_type: e_cacheL1C1; m: OBJSET_cacheL1C1; adr: Address);
    begin
      alias evt_entry: i_cacheL1C1[m].evt do
      alias pend_adr: i_cacheL1C1[m].evt.pend_adr do
    
        /* Check if the event type matches and the event still need to be served for this address */
        if evt_entry.event_queue[0].evt_type = cur_evt_type & MultisetCount(a: pend_adr, pend_adr[a] = adr) = 1 then
            MultisetRemovePred(a: pend_adr, pend_adr[a] = adr);
        endif;
    
      endalias;
      endalias;
    end;
    
    /* Event Ack: Checks if the currently pending event has been served by all addresses */
    function CheckInitEvent_cacheL1C1(cur_evt_type: e_cacheL1C1; m: OBJSET_cacheL1C1; adr: Address): boolean;
    begin
      alias evt_entry: i_cacheL1C1[m].evt do
      alias pend_adr: i_cacheL1C1[m].evt.pend_adr do
    
        if isundefined(evt_entry.event_queue[0].evt_type) then
            return false;
        endif;
    
        if evt_entry.event_queue[0].evt_type = cur_evt_type & MultisetCount(a:pend_adr, true) = 0 then
            return true;
        endif;
    
        return false;
    
      endalias;
      endalias;
    end;
    
    procedure ServeInitEvent_cacheL1C1(cur_evt_type: e_cacheL1C1; m: OBJSET_cacheL1C1; adr: Address);
    begin
      alias evt_entry: i_cacheL1C1[m].evt do
      alias pend_adr: i_cacheL1C1[m].evt.pend_adr do
    
        if evt_entry.event_queue[0].evt_type = cur_evt_type & MultisetCount(a:pend_adr, true) = 0 then
            PopEvent_cacheL1C1(m);
            NextEvent_cacheL1C1(m);
        endif;
    
      endalias;
      endalias;
    end;
    
    function TestAtomicEvent_cacheL1C1(m: OBJSET_cacheL1C1): boolean;
    begin
        if isundefined(i_cacheL1C1[m].evt.event_lock_adr) then
            return true;
        else
            return false;
        endif;
    end;
    
    procedure LockAtomicEvent_cacheL1C1(m: OBJSET_cacheL1C1; adr: Address);
    begin
      i_cacheL1C1[m].evt.event_lock_adr := adr;
    end;
    
    procedure UnlockAtomicEvent_cacheL1C1(m: OBJSET_cacheL1C1; adr: Address);
    begin
        if !isundefined(i_cacheL1C1[m].evt.event_lock_adr) then
            if i_cacheL1C1[m].evt.event_lock_adr = adr then
                undefine i_cacheL1C1[m].evt.event_lock_adr;
            endif;
        endif;
    end;
    
    procedure NextEvent_directoryL1C1(m: OBJSET_directoryL1C1);
    begin
      alias evt_entry: i_directoryL1C1[m].evt do
      alias evt_index: evt_entry.event_queue_index do
      alias pend_adr: evt_entry.pend_adr do
    
        if isundefined(evt_entry.event_queue[0].evt_type) then
            return;
        endif;
    
        if MultisetCount(a:pend_adr, true) > 0 then
          return;
        else
          if evt_entry.event_queue_index > 0 then
            for a: Address do
              if a != evt_entry.event_queue[0].evt_adr then
                MultisetAdd(a, pend_adr);
              endif;
            endfor;
          endif;
        endif;
    
      endalias;
      endalias;
      endalias;
    end;
    
    procedure PopEvent_directoryL1C1(m: OBJSET_directoryL1C1);
    begin
      alias evt_entry: i_directoryL1C1[m].evt do
      alias evt_index: evt_entry.event_queue_index do
    
        for i := 0 to evt_index-1 do
          if i < evt_index-1 then
            evt_entry.event_queue[i] := evt_entry.event_queue[i+1];
          else
            undefine evt_entry.event_queue[i];
          endif;
        endfor;
    
        evt_index := evt_index - 1;
    
      endalias;
      endalias;
    end;
    
    procedure ResetEvent_directoryL1C1();
    begin
      for m: OBJSET_directoryL1C1 do
        alias evt_entry: i_directoryL1C1[m].evt do
          undefine evt_entry.event_queue;
          evt_entry.event_queue_index := 0;
          undefine evt_entry.pend_adr;
          undefine evt_entry.event_lock_adr
        endalias;
      endfor;
    end;
    
    procedure IssueEvent_directoryL1C1(evt_type: e_directoryL1C1; m: OBJSET_directoryL1C1; adr: Address);
    begin
      alias evt_entry: i_directoryL1C1[m].evt do
      alias evt_index: evt_entry.event_queue_index do
    
        evt_entry.event_queue[evt_index].evt_type := evt_type;
        evt_entry.event_queue[evt_index].evt_adr := adr;
        evt_index := evt_index + 1;
    
        NextEvent_directoryL1C1(m);
    
      endalias;
      endalias;
    end;
    
    /* Event: Checks if the currently pending event has been served*/
    function CheckRemoteEvent_directoryL1C1(cur_evt_type: e_directoryL1C1; m: OBJSET_directoryL1C1; adr: Address): boolean;
    begin
      alias evt_entry: i_directoryL1C1[m].evt do
      alias pend_adr: i_directoryL1C1[m].evt.pend_adr do
    
        if isundefined(evt_entry.event_queue[0].evt_type) then
            return false;
        endif;
    
        /* Check if the event type matches and the event still need to be served for this address */
        if evt_entry.event_queue[0].evt_type = cur_evt_type & MultisetCount(a: pend_adr, pend_adr[a] = adr) = 1 then
            return true;
        endif;
    
        return false;
    
      endalias;
      endalias;
    end;
    
    procedure ServeRemoteEvent_directoryL1C1(cur_evt_type: e_directoryL1C1; m: OBJSET_directoryL1C1; adr: Address);
    begin
      alias evt_entry: i_directoryL1C1[m].evt do
      alias pend_adr: i_directoryL1C1[m].evt.pend_adr do
    
        /* Check if the event type matches and the event still need to be served for this address */
        if evt_entry.event_queue[0].evt_type = cur_evt_type & MultisetCount(a: pend_adr, pend_adr[a] = adr) = 1 then
            MultisetRemovePred(a: pend_adr, pend_adr[a] = adr);
        endif;
    
      endalias;
      endalias;
    end;
    
    /* Event Ack: Checks if the currently pending event has been served by all addresses */
    function CheckInitEvent_directoryL1C1(cur_evt_type: e_directoryL1C1; m: OBJSET_directoryL1C1; adr: Address): boolean;
    begin
      alias evt_entry: i_directoryL1C1[m].evt do
      alias pend_adr: i_directoryL1C1[m].evt.pend_adr do
    
        if isundefined(evt_entry.event_queue[0].evt_type) then
            return false;
        endif;
    
        if evt_entry.event_queue[0].evt_type = cur_evt_type & MultisetCount(a:pend_adr, true) = 0 then
            return true;
        endif;
    
        return false;
    
      endalias;
      endalias;
    end;
    
    procedure ServeInitEvent_directoryL1C1(cur_evt_type: e_directoryL1C1; m: OBJSET_directoryL1C1; adr: Address);
    begin
      alias evt_entry: i_directoryL1C1[m].evt do
      alias pend_adr: i_directoryL1C1[m].evt.pend_adr do
    
        if evt_entry.event_queue[0].evt_type = cur_evt_type & MultisetCount(a:pend_adr, true) = 0 then
            PopEvent_directoryL1C1(m);
            NextEvent_directoryL1C1(m);
        endif;
    
      endalias;
      endalias;
    end;
    
    function TestAtomicEvent_directoryL1C1(m: OBJSET_directoryL1C1): boolean;
    begin
        if isundefined(i_directoryL1C1[m].evt.event_lock_adr) then
            return true;
        else
            return false;
        endif;
    end;
    
    procedure LockAtomicEvent_directoryL1C1(m: OBJSET_directoryL1C1; adr: Address);
    begin
      i_directoryL1C1[m].evt.event_lock_adr := adr;
    end;
    
    procedure UnlockAtomicEvent_directoryL1C1(m: OBJSET_directoryL1C1; adr: Address);
    begin
        if !isundefined(i_directoryL1C1[m].evt.event_lock_adr) then
            if i_directoryL1C1[m].evt.event_lock_adr = adr then
                undefine i_directoryL1C1[m].evt.event_lock_adr;
            endif;
        endif;
    end;
    
    procedure ResetEvent_();
    begin
      ResetEvent_cacheL1C1();
      ResetEvent_directoryL1C1();
    
    end;
  ----Backend/Murphi/MurphiModular/Functions/GenPermFunc
    procedure Clear_perm(adr: Address; m: Machines);
    begin
      alias l_perm_set:g_perm[m][adr] do
          undefine l_perm_set;
      endalias;
    end;
    
    procedure Set_perm(acc_type: PermissionType; adr: Address; m: Machines);
    begin
      alias l_perm_set:g_perm[m][adr] do
      if MultiSetCount(i:l_perm_set, l_perm_set[i] = acc_type) = 0 then
          MultisetAdd(acc_type, l_perm_set);
      endif;
      endalias;
    end;
    
    procedure Reset_perm();
    begin
      for m:Machines do
        for adr:Address do
          Clear_perm(adr, m);
        endfor;
      endfor;
    end;
    
  
  ----Backend/Murphi/MurphiModular/Functions/GenFIFOFunc
  ----Backend/Murphi/MurphiModular/Functions/GenNetworkFunc
    procedure Send_fwd(msg:Message; src: Machines;);
      Assert(cnt_fwd[msg.dst] < O_NET_MAX) "Too many messages";
      fwd[msg.dst][cnt_fwd[msg.dst]] := msg;
      cnt_fwd[msg.dst] := cnt_fwd[msg.dst] + 1;
    end;
    
    procedure Pop_fwd(dst:Machines; src: Machines;);
    begin
      Assert (cnt_fwd[dst] > 0) "Trying to advance empty Q";
      for i := 0 to cnt_fwd[dst]-1 do
        if i < cnt_fwd[dst]-1 then
          fwd[dst][i] := fwd[dst][i+1];
        else
          undefine fwd[dst][i];
        endif;
      endfor;
      cnt_fwd[dst] := cnt_fwd[dst] - 1;
    end;
    
    procedure Send_resp(msg:Message; src: Machines;);
      Assert(cnt_resp[msg.dst] < O_NET_MAX) "Too many messages";
      resp[msg.dst][cnt_resp[msg.dst]] := msg;
      cnt_resp[msg.dst] := cnt_resp[msg.dst] + 1;
    end;
    
    procedure Pop_resp(dst:Machines; src: Machines;);
    begin
      Assert (cnt_resp[dst] > 0) "Trying to advance empty Q";
      for i := 0 to cnt_resp[dst]-1 do
        if i < cnt_resp[dst]-1 then
          resp[dst][i] := resp[dst][i+1];
        else
          undefine resp[dst][i];
        endif;
      endfor;
      cnt_resp[dst] := cnt_resp[dst] - 1;
    end;
    
    procedure Send_req(msg:Message; src: Machines;);
      Assert(cnt_req[msg.dst] < O_NET_MAX) "Too many messages";
      req[msg.dst][cnt_req[msg.dst]] := msg;
      cnt_req[msg.dst] := cnt_req[msg.dst] + 1;
    end;
    
    procedure Pop_req(dst:Machines; src: Machines;);
    begin
      Assert (cnt_req[dst] > 0) "Trying to advance empty Q";
      for i := 0 to cnt_req[dst]-1 do
        if i < cnt_req[dst]-1 then
          req[dst][i] := req[dst][i+1];
        else
          undefine req[dst][i];
        endif;
      endfor;
      cnt_req[dst] := cnt_req[dst] - 1;
    end;
    
    function req_network_ready(): boolean;
    begin
          for dst:Machines do
            for src: Machines do
              if cnt_req[dst] >= (O_NET_MAX-5) then
                return false;
              endif;
            endfor;
          endfor;
    
          return true;
    end;
    function resp_network_ready(): boolean;
    begin
          for dst:Machines do
            for src: Machines do
              if cnt_resp[dst] >= (O_NET_MAX-5) then
                return false;
              endif;
            endfor;
          endfor;
    
          return true;
    end;
    function fwd_network_ready(): boolean;
    begin
          for dst:Machines do
            for src: Machines do
              if cnt_fwd[dst] >= (O_NET_MAX-5) then
                return false;
              endif;
            endfor;
          endfor;
    
          return true;
    end;
    function network_ready(): boolean;
    begin
            if !req_network_ready() then
            return false;
          endif;
    
    
          if !resp_network_ready() then
            return false;
          endif;
    
    
          if !fwd_network_ready() then
            return false;
          endif;
    
    
    
      return true;
    end;
    
    procedure Reset_NET_();
    begin
      
      undefine resp;
      for dst:Machines do
          cnt_resp[dst] := 0;
      endfor;
      
      undefine req;
      for dst:Machines do
          cnt_req[dst] := 0;
      endfor;
      
      undefine fwd;
      for dst:Machines do
          cnt_fwd[dst] := 0;
      endfor;
    
    end;
    
  
  ----Backend/Murphi/MurphiModular/Functions/GenMessageConstrFunc
    function RequestL1C1(adr: Address; mtype: MessageType; src: Machines; dst: Machines) : Message;
    var Message: Message;
    begin
      Message.adr := adr;
      Message.mtype := mtype;
      Message.src := src;
      Message.dst := dst;
    return Message;
    end;
    
    function AckL1C1(adr: Address; mtype: MessageType; src: Machines; dst: Machines) : Message;
    var Message: Message;
    begin
      Message.adr := adr;
      Message.mtype := mtype;
      Message.src := src;
      Message.dst := dst;
    return Message;
    end;
    
    function RespL1C1(adr: Address; mtype: MessageType; src: Machines; dst: Machines; cl: ClValue) : Message;
    var Message: Message;
    begin
      Message.adr := adr;
      Message.mtype := mtype;
      Message.src := src;
      Message.dst := dst;
      Message.cl := cl;
    return Message;
    end;
    
  

--Backend/Murphi/MurphiModular/GenStateMachines

  ----Backend/Murphi/MurphiModular/StateMachines/GenAccessStateMachines
    procedure FSM_Access_cacheL1C1_I_acq_eventL1C1(adr:Address; m:OBJSET_cacheL1C1);
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      ServeRemoteEvent_cacheL1C1(cacheL1C1_acq_eventL1C1, m, adr);
      cbe.State := cacheL1C1_I;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_I_acquire(adr:Address; m:OBJSET_cacheL1C1);
    var msg: Message;
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      msg := RequestL1C1(adr, GetVL1C1, m, directoryL1C1);
      Send_req(msg, m);
      cbe.State := cacheL1C1_I_acquire;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_I_load(adr:Address; m:OBJSET_cacheL1C1);
    var msg: Message;
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      msg := RequestL1C1(adr, GetVL1C1, m, directoryL1C1);
      Send_req(msg, m);
      cbe.State := cacheL1C1_I_load;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_I_release(adr:Address; m:OBJSET_cacheL1C1);
    var msg: Message;
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      msg := RequestL1C1(adr, GetOL1C1, m, directoryL1C1);
      Send_req(msg, m);
      cbe.State := cacheL1C1_I_release;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_I_store(adr:Address; m:OBJSET_cacheL1C1);
    var msg: Message;
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      msg := RequestL1C1(adr, GetOL1C1, m, directoryL1C1);
      Send_req(msg, m);
      cbe.State := cacheL1C1_I_store;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_I_acquire_GetV_Ack_acq_eventL1C1(adr:Address; m:OBJSET_cacheL1C1);
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      Set_perm(load, adr, m);cbe.State := cacheL1C1_V;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_O_acq_eventL1C1(adr:Address; m:OBJSET_cacheL1C1);
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      ServeRemoteEvent_cacheL1C1(cacheL1C1_acq_eventL1C1, m, adr);
      cbe.State := cacheL1C1_O;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_O_acquire(adr:Address; m:OBJSET_cacheL1C1);
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      Set_perm(load, adr, m);cbe.State := cacheL1C1_O;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_O_evict(adr:Address; m:OBJSET_cacheL1C1);
    var msg: Message;
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      msg := RespL1C1(adr, PutOL1C1, m, directoryL1C1, cbe.cl);
      Send_req(msg, m);
      cbe.State := cacheL1C1_O_evict;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_O_load(adr:Address; m:OBJSET_cacheL1C1);
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      cbe.State := cacheL1C1_O;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_O_release(adr:Address; m:OBJSET_cacheL1C1);
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      Set_perm(store, adr, m);cbe.State := cacheL1C1_O;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_O_store(adr:Address; m:OBJSET_cacheL1C1);
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      cbe.State := cacheL1C1_O;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_V_acq_eventL1C1(adr:Address; m:OBJSET_cacheL1C1);
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      ServeRemoteEvent_cacheL1C1(cacheL1C1_acq_eventL1C1, m, adr);
      cbe.State := cacheL1C1_I;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_V_acquire(adr:Address; m:OBJSET_cacheL1C1);
    var msg: Message;
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      msg := RequestL1C1(adr, GetVL1C1, m, directoryL1C1);
      Send_req(msg, m);
      cbe.State := cacheL1C1_V_acquire;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_V_evict(adr:Address; m:OBJSET_cacheL1C1);
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      cbe.State := cacheL1C1_I;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_V_load(adr:Address; m:OBJSET_cacheL1C1);
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      cbe.State := cacheL1C1_V;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_V_release(adr:Address; m:OBJSET_cacheL1C1);
    var msg: Message;
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      msg := RequestL1C1(adr, GetOL1C1, m, directoryL1C1);
      Send_req(msg, m);
      cbe.State := cacheL1C1_V_release;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_V_store(adr:Address; m:OBJSET_cacheL1C1);
    var msg: Message;
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      msg := RequestL1C1(adr, GetOL1C1, m, directoryL1C1);
      Send_req(msg, m);
      cbe.State := cacheL1C1_V_store;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_V_acquire_GetV_Ack_acq_eventL1C1(adr:Address; m:OBJSET_cacheL1C1);
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      Set_perm(load, adr, m);cbe.State := cacheL1C1_V;
    endalias;
    end;
    
    procedure FSM_Access_directoryL1C1_I_acq_eventL1C1(adr:Address; m:OBJSET_directoryL1C1);
    begin
    alias cbe: i_directoryL1C1[m].cb[adr] do
      ServeRemoteEvent_directoryL1C1(directoryL1C1_acq_eventL1C1, m, adr);
      cbe.State := directoryL1C1_I;
    endalias;
    end;
    
    procedure FSM_Access_directoryL1C1_I_release(adr:Address; m:OBJSET_directoryL1C1);
    var msg_GetOL1: Message;
    var msg_GetO_AckL1: Message;
    var msg_PutOL1: Message;
    var msg_PutO_AckL1: Message;
    begin
    alias cbe: i_directoryL1C1[m].cb[adr] do
      msg_GetOL1 := RequestL1C1(adr, GetOL1C1, m, m);
      msg_GetO_AckL1 := RespL1C1(adr, GetO_AckL1C1, m, msg_GetOL1.src, cbe.cl);
      cbe.ownerL1C1 := msg_GetOL1.src;
      cbe.cl := msg_GetO_AckL1.cl;
      Set_perm(store, adr, m);msg_PutOL1 := RespL1C1(adr, PutOL1C1, m, m, cbe.cl);
      msg_PutO_AckL1 := AckL1C1(adr, PutO_AckL1C1, m, msg_PutOL1.src);
      if !(cbe.ownerL1C1 = msg_PutOL1.src) then
      cbe.State := directoryL1C1_I;
      endif
    endalias;
    end;
    
    procedure FSM_Access_directoryL1C1_I_store(adr:Address; m:OBJSET_directoryL1C1);
    var msg_GetOL1: Message;
    var msg_GetO_AckL1: Message;
    var msg_PutOL1: Message;
    var msg_PutO_AckL1: Message;
    begin
    alias cbe: i_directoryL1C1[m].cb[adr] do
      msg_GetOL1 := RequestL1C1(adr, GetOL1C1, m, m);
      msg_GetO_AckL1 := RespL1C1(adr, GetO_AckL1C1, m, msg_GetOL1.src, cbe.cl);
      cbe.ownerL1C1 := msg_GetOL1.src;
      cbe.cl := msg_GetO_AckL1.cl;
      msg_PutOL1 := RespL1C1(adr, PutOL1C1, m, m, cbe.cl);
      msg_PutO_AckL1 := AckL1C1(adr, PutO_AckL1C1, m, msg_PutOL1.src);
      if (cbe.ownerL1C1 = msg_PutOL1.src) then
      cbe.cl := msg_PutOL1.cl;
      cbe.State := directoryL1C1_I;
      endif
    endalias;
    end;
    
    procedure FSM_Access_directoryL1C1_O_acq_eventL1C1(adr:Address; m:OBJSET_directoryL1C1);
    begin
    alias cbe: i_directoryL1C1[m].cb[adr] do
      ServeRemoteEvent_directoryL1C1(directoryL1C1_acq_eventL1C1, m, adr);
      cbe.State := directoryL1C1_O;
    endalias;
    end;
    
    procedure FSM_Access_directoryL1C1_O_release(adr:Address; m:OBJSET_directoryL1C1);
    var msg_GetOL1: Message;
    var msg: Message;
    begin
    alias cbe: i_directoryL1C1[m].cb[adr] do
      -- [Axiom 12] non-coherent access at directory on Coherent-Writable State sends a downgrade
      assert isundefined(cbe.coherentWriteFlag) ">[Axiom 12] directory on O; getting a request contending for O data. Expected to not overlap with another event!\n";
      cbe.coherentWriteFlag := true;
      cbe.previous_ownerL1C1 := cbe.ownerL1C1;

      msg_GetOL1 := RequestL1C1(adr, GetOL1C1, m, m);
      msg := RequestL1C1(adr, Fwd_GetOL1C1, msg_GetOL1.src, cbe.ownerL1C1);

      assert (msg.dst = cbe.ownerL1C1) ">[Axiom 9] Directory: O request's fwd-downgrade on O must be to the Owner!\n";

      Send_fwd(msg, m);
      cbe.ownerL1C1 := msg_GetOL1.src;
      cbe.State := directoryL1C1_dO_GetO_x_pI_release;
    endalias;
    end;
    
    procedure FSM_Access_directoryL1C1_O_store(adr:Address; m:OBJSET_directoryL1C1);
    var msg_GetOL1: Message;
    var msg: Message;
    begin
    alias cbe: i_directoryL1C1[m].cb[adr] do
      -- [Axiom 12] non-coherent access at directory on Coherent-Writable State sends a downgrade
      assert isundefined(cbe.coherentWriteFlag) ">[Axiom 12] directory on O; getting a request contending for O data. Expected to not overlap with another event!\n";
      cbe.coherentWriteFlag := true;
      cbe.previous_ownerL1C1 := cbe.ownerL1C1;

      msg_GetOL1 := RequestL1C1(adr, GetOL1C1, m, m);
      msg := RequestL1C1(adr, Fwd_GetOL1C1, msg_GetOL1.src, cbe.ownerL1C1);

      assert (msg.dst = cbe.ownerL1C1) ">[Axiom 9] Directory: O request's fwd-downgrade on O must be to the Owner!\n";

      Send_fwd(msg, m);
      cbe.ownerL1C1 := msg_GetOL1.src;
      cbe.State := directoryL1C1_dO_GetO_x_pI_store;
    endalias;
    end;
    
  ----Backend/Murphi/MurphiModular/StateMachines/GenMessageStateMachines
    function FSM_MSG_cacheL1C1(inmsg:Message; m:OBJSET_cacheL1C1) : boolean;
    var msg: Message;
    begin
      alias adr: inmsg.adr do
      alias cbe: i_cacheL1C1[m].cb[adr] do
    switch cbe.State
      case cacheL1C1_I:
      switch inmsg.mtype
        else return false;
      endswitch;
      
      case cacheL1C1_I_acquire:
      switch inmsg.mtype
        case GetV_AckL1C1:
          cbe.cl := inmsg.cl;
          IssueEvent_cacheL1C1(cacheL1C1_acq_eventL1C1, m, adr);
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_I_acquire_GetV_Ack;
          return true;
        
        else return false;
      endswitch;
      
      case cacheL1C1_I_acquire_GetV_Ack:
      switch inmsg.mtype
        else return false;
      endswitch;
      
      case cacheL1C1_I_load:
      switch inmsg.mtype
        case GetV_AckL1C1:
          cbe.cl := inmsg.cl;
          Clear_perm(adr, m); Set_perm(load, adr, m);
          cbe.State := cacheL1C1_V;
          return true;
        
        else return false;
      endswitch;
      
      case cacheL1C1_I_release:
      switch inmsg.mtype
        case GetO_AckL1C1:
          cbe.cl := inmsg.cl;
          Set_perm(store, adr, m);
          Clear_perm(adr, m); Set_perm(load, adr, m); Set_perm(store, adr, m);
          cbe.State := cacheL1C1_O;
          return true;
        
        else return false;
      endswitch;
      
      case cacheL1C1_I_store:
      switch inmsg.mtype
        case GetO_AckL1C1:
          cbe.cl := inmsg.cl;
          Clear_perm(adr, m); Set_perm(load, adr, m); Set_perm(store, adr, m);
          cbe.State := cacheL1C1_O;
          return true;
        
        else return false;
      endswitch;
      
      case cacheL1C1_O:
      switch inmsg.mtype
        case Fwd_GetOL1C1:
          msg := RespL1C1(adr,WB_AckL1C1,inmsg.src,directoryL1C1,cbe.cl);
          Send_resp(msg, m);
          Clear_perm(adr, m); Set_perm(load, adr, m);
          cbe.State := cacheL1C1_V;

          -- [Axiom 9 / 12]
          alias dir_cbe: i_directoryL1C1[directoryL1C1].cb[adr] do
            assert (dir_cbe.coherentWriteFlag) ">[Axiom 9/12] Cache: Got downgrade, expected Directory to have sent it!\n";
            assert (dir_cbe.previous_ownerL1C1 = m) ">[Axiom 9/12] Cache: downgrade, expected downgrade to be for `previous` Owner?!\n";
            undefine dir_cbe.coherentWriteFlag;
            undefine dir_cbe.previous_ownerL1C1;
          endalias;
          return true;
        
        else return false;
      endswitch;
      
      case cacheL1C1_O_evict:
      switch inmsg.mtype
        case Fwd_GetOL1C1:
          msg := RespL1C1(adr,WB_AckL1C1,inmsg.src,directoryL1C1,cbe.cl);
          Send_resp(msg, m);
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_O_evict_x_V;

          -- [Axiom 9 / 12]
          alias dir_cbe: i_directoryL1C1[directoryL1C1].cb[adr] do
            assert (dir_cbe.coherentWriteFlag) ">[Axiom 9/12] Cache (evicting): Got downgrade, expected Directory to have sent it!\n";
            assert (dir_cbe.previous_ownerL1C1 = m) ">[Axiom 9/12] Cache (evicting): downgrade, expected downgrade to be for `previous` Owner?!\n";
            undefine dir_cbe.coherentWriteFlag;
            undefine dir_cbe.previous_ownerL1C1;
          endalias;
          return true;
        
        case PutO_AckL1C1:
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_I;
          return true;
        
        else return false;
      endswitch;
      
      case cacheL1C1_O_evict_x_V:
      switch inmsg.mtype
        case PutO_AckL1C1:
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_I;
          return true;
        
        else return false;
      endswitch;
      
      case cacheL1C1_V:
      switch inmsg.mtype
        else return false;
      endswitch;
      
      case cacheL1C1_V_acquire:
      switch inmsg.mtype
        case GetV_AckL1C1:
          cbe.cl := inmsg.cl;
          IssueEvent_cacheL1C1(cacheL1C1_acq_eventL1C1, m, adr);
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_V_acquire_GetV_Ack;
          return true;
        
        else return false;
      endswitch;
      
      case cacheL1C1_V_acquire_GetV_Ack:
      switch inmsg.mtype
        else return false;
      endswitch;
      
      case cacheL1C1_V_release:
      switch inmsg.mtype
        case GetO_AckL1C1:
          cbe.cl := inmsg.cl;
          Set_perm(store, adr, m);
          Clear_perm(adr, m); Set_perm(load, adr, m); Set_perm(store, adr, m);
          cbe.State := cacheL1C1_O;
          return true;
        
        else return false;
      endswitch;
      
      case cacheL1C1_V_store:
      switch inmsg.mtype
        case GetO_AckL1C1:
          cbe.cl := inmsg.cl;
          Clear_perm(adr, m); Set_perm(load, adr, m); Set_perm(store, adr, m);
          cbe.State := cacheL1C1_O;
          return true;
        
        else return false;
      endswitch;
      
    endswitch;
    endalias;
    endalias;
    return false;
    end;
    
    function FSM_MSG_directoryL1C1(inmsg:Message; m:OBJSET_directoryL1C1) : boolean;
    var msg: Message;
    var msg_GetO_AckL1: Message;
    var msg_PutOL1: Message;
    var msg_PutO_AckL1: Message;
    var shim_to_global_msg : Message;
    begin
      alias adr: inmsg.adr do
      alias cbe: i_directoryL1C1[m].cb[adr] do
    switch cbe.State
      -- [Shim Transient]
      case directoryL1C1_I_to_O_shim_complete:
      switch inmsg.mtype
        case GetOL1C1:
          -- [Cluster to Global Shim]
          -- transient state for global shim request.
          -- put "I to O shim complete\n";
          msg := RespL1C1(adr,GetO_AckL1C1,m,inmsg.src,cbe.cl);
          Send_resp(msg, m);
          cbe.ownerL1C1 := inmsg.src;
          Clear_perm(adr, m);
          cbe.State := directoryL1C1_O;
          return true;
        
        else return false;
      endswitch;

      case directoryL1C1_I_to_V_shim_complete:
      switch inmsg.mtype
        case GetVL1C1:
          -- [Cluster to Global Shim]
          -- transient state for global shim request.
          -- put "I to V shim complete\n";
          msg := RespL1C1(adr,GetV_AckL1C1,m,inmsg.src,cbe.cl);
          Send_resp(msg, m);
          Clear_perm(adr, m);
          cbe.State := directoryL1C1_V;
          return true;
        
        else return false;
      endswitch;

      case directoryL1C1_I:
      switch inmsg.mtype
        case GetOL1C1:
          -- [Cluster to Global Shim]
          -- transient state for global shim request.
          -- [Shim Axiom 15]
          shim_to_global_msg.mtype := GetOL1C1;
          assert (shim_to_global_msg.mtype = GetOL1C1) "A Directory O request on I -> Produce Global Get M\n";
          cbe.State := directoryL1C1_I_to_O_shim_transient;
          return false;

        case GetVL1C1:
          -- put "I to V shim transient\n";
          -- [Shim Axiom 15]
          shim_to_global_msg.mtype := GetVL1C1;
          assert (shim_to_global_msg.mtype = GetVL1C1) "A Directory V request on I -> Produce Global Get S\n";
          cbe.State := directoryL1C1_I_to_V_shim_transient;
          return false;
        
        case PutOL1C1:
          -- [NOTE] the directory on I can just consume the PutO
          msg := AckL1C1(adr,PutO_AckL1C1,m,inmsg.src);
          Send_fwd(msg, m);
          Clear_perm(adr, m);
          cbe.State := directoryL1C1_I;
          return true;
        
        else return false;
      endswitch;
      
      case directoryL1C1_O:
      switch inmsg.mtype
        case GetOL1C1:
          -- [Axiom 9] coherent write at directory on Coherent-Writable State sends a downgrade
          assert isundefined(cbe.coherentWriteFlag) ">[Axiom 9]";
          cbe.coherentWriteFlag := true;
          cbe.previous_ownerL1C1 := cbe.ownerL1C1;

          msg := RequestL1C1(adr,Fwd_GetOL1C1,inmsg.src,cbe.ownerL1C1);

          assert (msg.dst = cbe.ownerL1C1) ">[Axiom 9] Directory: O request's fwd-downgrade on O must be to the Owner!\n";

          Send_fwd(msg, m);
          cbe.ownerL1C1 := inmsg.src;
          Clear_perm(adr, m);
          cbe.State := directoryL1C1_O_GetO;
          return true;
        
        case GetVL1C1:
          -- [Axiom 12] non-coherent access at directory on Coherent-Writable State sends a downgrade
          assert isundefined(cbe.coherentWriteFlag) ">[Axiom 12]";
          cbe.coherentWriteFlag := true;
          cbe.previous_ownerL1C1 := cbe.ownerL1C1;

          msg := RequestL1C1(adr,Fwd_GetOL1C1,inmsg.src,cbe.ownerL1C1);

          assert (msg.dst = cbe.ownerL1C1) ">[Axiom 12] Directory: O request's fwd-downgrade on O must be to the Owner!\n";

          Send_fwd(msg, m);
          Clear_perm(adr, m);
          cbe.State := directoryL1C1_O_GetV;
          return true;
        
        case PutOL1C1:
          msg := AckL1C1(adr,PutO_AckL1C1,m,inmsg.src);
          Send_fwd(msg, m);
          if !(cbe.ownerL1C1 = inmsg.src) then
            Clear_perm(adr, m);
            cbe.State := directoryL1C1_I;
            return true;
          endif;
          if (cbe.ownerL1C1 = inmsg.src) then
            cbe.cl := inmsg.cl;
            Clear_perm(adr, m);
            cbe.State := directoryL1C1_I;
            return true;
          endif;
        
        else return false;
      endswitch;
      
      case directoryL1C1_O_GetO:
      switch inmsg.mtype
        case WB_AckL1C1:
          msg := RespL1C1(adr,GetO_AckL1C1,m,inmsg.src,inmsg.cl);
          Send_resp(msg, m);
          Clear_perm(adr, m);
          cbe.State := directoryL1C1_O;
          return true;
        
        else return false;
      endswitch;
      
      case directoryL1C1_O_GetV:
      switch inmsg.mtype
        case WB_AckL1C1:
          cbe.cl := inmsg.cl;
          msg := RespL1C1(adr,GetV_AckL1C1,m,inmsg.src,cbe.cl);
          Send_resp(msg, m);
          Clear_perm(adr, m);
          cbe.State := directoryL1C1_V;
          return true;
        
        else return false;
      endswitch;
      
      case directoryL1C1_V_to_O_shim_complete:
      switch inmsg.mtype
        case GetOL1C1:
          -- [Cluster to Global Shim]
          -- transient state for global shim request.
          -- put "V to O shim complete\n";
          msg := RespL1C1(adr,GetO_AckL1C1,m,inmsg.src,cbe.cl);
          Send_resp(msg, m);
          cbe.ownerL1C1 := inmsg.src;
          Clear_perm(adr, m);
          cbe.State := directoryL1C1_O;
          return true;
        
        else return false;
      endswitch;

      case directoryL1C1_V:
      switch inmsg.mtype
        case GetOL1C1:
          -- go to transient
          -- put "V to O shim transient\n";
          -- [Shim Axiom 15]
          shim_to_global_msg.mtype := GetOL1C1;
          assert (shim_to_global_msg.mtype = GetOL1C1) "A Directory O request on V -> Produce Global Get M\n";
          cbe.State := directoryL1C1_V_to_O_shim_transient;
          return false;
        
        case GetVL1C1:
          msg := RespL1C1(adr,GetV_AckL1C1,m,inmsg.src,cbe.cl);
          Send_resp(msg, m);
          Clear_perm(adr, m);
          cbe.State := directoryL1C1_V;
          return true;
        
        case PutOL1C1:
          msg := AckL1C1(adr,PutO_AckL1C1,m,inmsg.src);
          Send_fwd(msg, m);
          Clear_perm(adr, m);
          cbe.State := directoryL1C1_V;
          return true;
        
        else return false;
      endswitch;
      
      case directoryL1C1_dO_GetO_x_pI_release:
      switch inmsg.mtype
        case WB_AckL1C1:
          msg_GetO_AckL1 := RespL1C1(adr,GetO_AckL1C1,m,inmsg.src,inmsg.cl);
          cbe.cl := msg_GetO_AckL1.cl;
          Set_perm(store, adr, m);
          msg_PutOL1 := RespL1C1(adr,PutOL1C1,m,m,cbe.cl);
          msg_PutO_AckL1 := AckL1C1(adr,PutO_AckL1C1,m,msg_PutOL1.src);
          if !(cbe.ownerL1C1 = msg_PutOL1.src) then
            Clear_perm(adr, m);
            cbe.State := directoryL1C1_I;
            -- [Shim Axiom 16]: Global to Cluster downgrade translation
            assert (cbe.State = directoryL1C1_I) ">[Shim Axiom 16] Global to Cluster Downgrade. Expected Directory State to go to I after getting a WriteBack Response from Cache.\n";
            return true;
          endif;
          if (cbe.ownerL1C1 = msg_PutOL1.src) then
            cbe.cl := msg_PutOL1.cl;
            Clear_perm(adr, m);
            cbe.State := directoryL1C1_I;
            -- [Shim Axiom 16]: Global to Cluster downgrade translation
            assert (cbe.State = directoryL1C1_I) ">[Shim Axiom 16] Global to Cluster Downgrade. Expected Directory State to go to I after getting a WriteBack Response from Cache.\n";
            return true;
          endif;
        
        else return false;
      endswitch;
      
      case directoryL1C1_dO_GetO_x_pI_store:
      switch inmsg.mtype
        case WB_AckL1C1:
          msg_GetO_AckL1 := RespL1C1(adr,GetO_AckL1C1,m,inmsg.src,inmsg.cl);
          cbe.cl := msg_GetO_AckL1.cl;
          msg_PutOL1 := RespL1C1(adr,PutOL1C1,m,m,cbe.cl);
          msg_PutO_AckL1 := AckL1C1(adr,PutO_AckL1C1,m,msg_PutOL1.src);
          if (cbe.ownerL1C1 = msg_PutOL1.src) then
            cbe.cl := msg_PutOL1.cl;
            Clear_perm(adr, m);
            cbe.State := directoryL1C1_I;
            -- [Shim Axiom 16]: Global to Cluster downgrade translation
            assert (cbe.State = directoryL1C1_I) ">[Shim Axiom 16] Global to Cluster Downgrade. Expected Directory State to go to I after getting a WriteBack Response from Cache.\n";
            return true;
          endif;
          if !(cbe.ownerL1C1 = msg_PutOL1.src) then
            Clear_perm(adr, m);
            cbe.State := directoryL1C1_I;
            -- [Shim Axiom 16]: Global to Cluster downgrade translation
            assert (cbe.State = directoryL1C1_I) ">[Shim Axiom 16] Global to Cluster Downgrade. Expected Directory State to go to I after getting a WriteBack Response from Cache.\n";
            return true;
          endif;
        
        else return false;
      endswitch;
      
    endswitch;
    endalias;
    endalias;
    return false;
    end;
    

--Backend/Murphi/MurphiModular/GenResetFunc

  procedure System_Reset();
  begin
  Reset_perm();
  Reset_NET_();
  ResetMachine_();
  ResetEvent_();
  end;
  

--Backend/Murphi/MurphiModular/GenRules
  ----Backend/Murphi/MurphiModular/Rules/GenAccessRuleSet
    ruleset m:OBJSET_cacheL1C1 do
    ruleset adr:Address do
      alias cbe:i_cacheL1C1[m].cb[adr] do
    
      rule "cacheL1C1_I_acquire"
        cbe.State = cacheL1C1_I & network_ready() & TestAtomicEvent_cacheL1C1(m)
      ==>
        FSM_Access_cacheL1C1_I_acquire(adr, m);
        LockAtomicEvent_cacheL1C1(m, adr);
      endrule;
    
      rule "cacheL1C1_I_release"
        cbe.State = cacheL1C1_I & network_ready() 
      ==>
        FSM_Access_cacheL1C1_I_release(adr, m);
        
      endrule;
    
      rule "cacheL1C1_I_load"
        cbe.State = cacheL1C1_I & network_ready() 
      ==>
        FSM_Access_cacheL1C1_I_load(adr, m);
        
      endrule;
    
      rule "cacheL1C1_I_store"
        cbe.State = cacheL1C1_I & network_ready() 
      ==>
        FSM_Access_cacheL1C1_I_store(adr, m);
        
      endrule;
    
      rule "cacheL1C1_O_acquire"
        cbe.State = cacheL1C1_O 
      ==>
        FSM_Access_cacheL1C1_O_acquire(adr, m);
        
      endrule;
    
      rule "cacheL1C1_O_evict"
        cbe.State = cacheL1C1_O & network_ready() 
      ==>
        FSM_Access_cacheL1C1_O_evict(adr, m);
        
      endrule;
    
      rule "cacheL1C1_O_load"
        cbe.State = cacheL1C1_O 
      ==>
        FSM_Access_cacheL1C1_O_load(adr, m);
        
      endrule;
    
      rule "cacheL1C1_O_release"
        cbe.State = cacheL1C1_O 
      ==>
        FSM_Access_cacheL1C1_O_release(adr, m);
        
      endrule;
    
      rule "cacheL1C1_O_store"
        cbe.State = cacheL1C1_O 
      ==>
        FSM_Access_cacheL1C1_O_store(adr, m);
        
      endrule;
    
      rule "cacheL1C1_V_store"
        cbe.State = cacheL1C1_V & network_ready() 
      ==>
        FSM_Access_cacheL1C1_V_store(adr, m);
        
      endrule;
    
      rule "cacheL1C1_V_acquire"
        cbe.State = cacheL1C1_V & network_ready() & TestAtomicEvent_cacheL1C1(m)
      ==>
        FSM_Access_cacheL1C1_V_acquire(adr, m);
        LockAtomicEvent_cacheL1C1(m, adr);
      endrule;
    
      rule "cacheL1C1_V_release"
        cbe.State = cacheL1C1_V & network_ready() 
      ==>
        FSM_Access_cacheL1C1_V_release(adr, m);
        
      endrule;
    
      rule "cacheL1C1_V_load"
        cbe.State = cacheL1C1_V 
      ==>
        FSM_Access_cacheL1C1_V_load(adr, m);
        
      endrule;
    
      rule "cacheL1C1_V_evict"
        cbe.State = cacheL1C1_V 
      ==>
        FSM_Access_cacheL1C1_V_evict(adr, m);
        
      endrule;
    
    
      endalias;
    endruleset;
    endruleset;
    
    ruleset m:OBJSET_directoryL1C1 do
    ruleset adr:Address do
      alias cbe:i_directoryL1C1[m].cb[adr] do
    
      rule "directoryL1C1_I_to_O_shim_global_complete"
        cbe.State = directoryL1C1_I_to_O_shim_transient
      ==>
        cbe.State := directoryL1C1_I_to_O_shim_complete;
      endrule;
    
      rule "directoryL1C1_I_to_V_shim_global_complete"
        cbe.State = directoryL1C1_I_to_V_shim_transient
      ==>
        cbe.State := directoryL1C1_I_to_V_shim_complete;
      endrule;
    
      rule "directoryL1C1_V_to_O_shim_global_complete"
        cbe.State = directoryL1C1_V_to_O_shim_transient
      ==>
        cbe.State := directoryL1C1_V_to_O_shim_complete;
      endrule;

      rule "directoryL1C1_I_release"
        cbe.State = directoryL1C1_I 
      ==>
        FSM_Access_directoryL1C1_I_release(adr, m);
        
      endrule;
    
      rule "directoryL1C1_I_store"
        cbe.State = directoryL1C1_I 
      ==>
        FSM_Access_directoryL1C1_I_store(adr, m);
        
      endrule;
    
      rule "directoryL1C1_V_release"
        cbe.State = directoryL1C1_V 
      ==>
        -- [Shim Axiom 16]: Global to Cluster downgrade translation
        FSM_Access_directoryL1C1_I_release(adr, m);
        
      endrule;
    
      rule "directoryL1C1_V_store"
        cbe.State = directoryL1C1_V 
      ==>
        -- [Shim Axiom 16]: Global to Cluster downgrade translation
        FSM_Access_directoryL1C1_I_store(adr, m);
        
      endrule;
    
      rule "directoryL1C1_O_release"
        cbe.State = directoryL1C1_O & network_ready() 
      ==>
        FSM_Access_directoryL1C1_O_release(adr, m);
        -- [Shim Axiom 16]: Global to Cluster downgrade translation
        assert (cbe.State != directoryL1C1_O) "Global to Cluster translation on O; directory still on O state; But expected to be on a transient state to handle the downgrade.";
        
      endrule;
    
      rule "directoryL1C1_O_store"
        cbe.State = directoryL1C1_O & network_ready() 
      ==>
        FSM_Access_directoryL1C1_O_store(adr, m);
        -- [Shim Axiom 16]: Global to Cluster downgrade translation
        assert (cbe.State != directoryL1C1_O) "Global to Cluster translation on O; directory still on O state; But expected to be on a transient state to handle the downgrade.";
        
      endrule;
    
    
      endalias;
    endruleset;
    endruleset;
    
  ----Backend/Murphi/MurphiModular/Rules/GenEventRuleSet
    ruleset m:OBJSET_cacheL1C1 do
    ruleset adr:Address do
      alias cbe:i_cacheL1C1[m].cb[adr] do
    
      rule "cacheL1C1_I_acq_eventL1C1"
        cbe.State = cacheL1C1_I & CheckRemoteEvent_cacheL1C1(cacheL1C1_acq_eventL1C1, m, adr) 
      ==>
        FSM_Access_cacheL1C1_I_acq_eventL1C1(adr, m);
      endrule;
    
      rule "cacheL1C1_I_acquire_GetV_Ack_acq_eventL1C1"
        cbe.State = cacheL1C1_I_acquire_GetV_Ack & CheckInitEvent_cacheL1C1(cacheL1C1_acq_eventL1C1, m, adr) 
      ==>
        ServeInitEvent_cacheL1C1(cacheL1C1_acq_eventL1C1, m, adr);
        FSM_Access_cacheL1C1_I_acquire_GetV_Ack_acq_eventL1C1(adr, m);
      endrule;
    
      rule "cacheL1C1_O_acq_eventL1C1"
        cbe.State = cacheL1C1_O & CheckRemoteEvent_cacheL1C1(cacheL1C1_acq_eventL1C1, m, adr) 
      ==>
        FSM_Access_cacheL1C1_O_acq_eventL1C1(adr, m);
      endrule;
    
      rule "cacheL1C1_V_acq_eventL1C1"
        cbe.State = cacheL1C1_V & CheckRemoteEvent_cacheL1C1(cacheL1C1_acq_eventL1C1, m, adr) 
      ==>
        FSM_Access_cacheL1C1_V_acq_eventL1C1(adr, m);
      endrule;
    
      rule "cacheL1C1_V_acquire_GetV_Ack_acq_eventL1C1"
        cbe.State = cacheL1C1_V_acquire_GetV_Ack & CheckInitEvent_cacheL1C1(cacheL1C1_acq_eventL1C1, m, adr) 
      ==>
        ServeInitEvent_cacheL1C1(cacheL1C1_acq_eventL1C1, m, adr);
        FSM_Access_cacheL1C1_V_acquire_GetV_Ack_acq_eventL1C1(adr, m);
      endrule;
    
    
      endalias;
    endruleset;
    endruleset;
    
    ruleset m:OBJSET_cacheL1C1 do
    ruleset adr:Address do
      alias cbe:i_cacheL1C1[m].cb[adr] do
    
    rule "cacheL1C1_I_UnlockAtomicEvent_"
      cbe.State = cacheL1C1_I
    ==>
      UnlockAtomicEvent_cacheL1C1(m, adr);
    endrule;
    rule "cacheL1C1_V_UnlockAtomicEvent_"
      cbe.State = cacheL1C1_V
    ==>
      UnlockAtomicEvent_cacheL1C1(m, adr);
    endrule;
    rule "cacheL1C1_O_UnlockAtomicEvent_"
      cbe.State = cacheL1C1_O
    ==>
      UnlockAtomicEvent_cacheL1C1(m, adr);
    endrule;
    
      endalias;
    endruleset;
    endruleset;
    
    ruleset m:OBJSET_directoryL1C1 do
    ruleset adr:Address do
      alias cbe:i_directoryL1C1[m].cb[adr] do
    
      rule "directoryL1C1_I_acq_eventL1C1"
        cbe.State = directoryL1C1_I & CheckRemoteEvent_directoryL1C1(directoryL1C1_acq_eventL1C1, m, adr) 
      ==>
        FSM_Access_directoryL1C1_I_acq_eventL1C1(adr, m);
      endrule;
    
      rule "directoryL1C1_O_acq_eventL1C1"
        cbe.State = directoryL1C1_O & CheckRemoteEvent_directoryL1C1(directoryL1C1_acq_eventL1C1, m, adr) 
      ==>
        FSM_Access_directoryL1C1_O_acq_eventL1C1(adr, m);
      endrule;
    
    
      endalias;
    endruleset;
    endruleset;
    
    ruleset m:OBJSET_directoryL1C1 do
    ruleset adr:Address do
      alias cbe:i_directoryL1C1[m].cb[adr] do
    
    rule "directoryL1C1_I_UnlockAtomicEvent_"
      cbe.State = directoryL1C1_I
    ==>
      UnlockAtomicEvent_directoryL1C1(m, adr);
    endrule;
    rule "directoryL1C1_O_UnlockAtomicEvent_"
      cbe.State = directoryL1C1_O
    ==>
      UnlockAtomicEvent_directoryL1C1(m, adr);
    endrule;
    
      endalias;
    endruleset;
    endruleset;
    
  ----Backend/Murphi/MurphiModular/Rules/GenNetworkRule
    ruleset dst:Machines do
        ruleset src: Machines do
            alias msg:resp[dst][0] do
              rule "Receive resp"
                cnt_resp[dst] > 0
              ==>
            if IsMember(dst, OBJSET_directoryL1C1) then
              if FSM_MSG_directoryL1C1(msg, dst) then
                  Pop_resp(dst, src);
              endif;
            elsif IsMember(dst, OBJSET_cacheL1C1) then
              if FSM_MSG_cacheL1C1(msg, dst) then
                  Pop_resp(dst, src);
              endif;
            else error "unknown machine";
            endif;
    
              endrule;
            endalias;
        endruleset;
    endruleset;
    
    ruleset dst:Machines do
        ruleset src: Machines do
            alias msg:req[dst][0] do
              rule "Receive req"
                cnt_req[dst] > 0
              ==>
            if IsMember(dst, OBJSET_directoryL1C1) then
              if FSM_MSG_directoryL1C1(msg, dst) then
                  Pop_req(dst, src);
              endif;
            elsif IsMember(dst, OBJSET_cacheL1C1) then
              if FSM_MSG_cacheL1C1(msg, dst) then
                  Pop_req(dst, src);
              endif;
            else error "unknown machine";
            endif;
    
              endrule;
            endalias;
        endruleset;
    endruleset;
    
    ruleset dst:Machines do
        ruleset src: Machines do
            alias msg:fwd[dst][0] do
              rule "Receive fwd"
                cnt_fwd[dst] > 0
              ==>
            if IsMember(dst, OBJSET_directoryL1C1) then
              if FSM_MSG_directoryL1C1(msg, dst) then
                  Pop_fwd(dst, src);
              endif;
            elsif IsMember(dst, OBJSET_cacheL1C1) then
              if FSM_MSG_cacheL1C1(msg, dst) then
                  Pop_fwd(dst, src);
              endif;
            else error "unknown machine";
            endif;
    
              endrule;
            endalias;
        endruleset;
    endruleset;
    

--Backend/Murphi/MurphiModular/GenStartStates

  startstate
    System_Reset();
  endstartstate;

--Backend/Murphi/MurphiModular/GenInvariant
