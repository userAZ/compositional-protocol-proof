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
        none
      };
      
      ------Backend/Murphi/MurphiModular/Types/Enums/SubEnums/GenMessageTypes
      MessageType: enum {
        RdOwnL1C1, 
        RdSharedL1C1, 
        RspIHitSEL1C1, 
        CleanEvictNoDataL1C1, 
        RspSHitSEL1C1, 
        RspSFwdML1C1, 
        DevDataMsgL1C1, 
        RspIFwdML1C1, 
        DirtyEvictL1C1, 
        GO_SL1C1, 
        HostDataMsgL1C1, 
        GO_EL1C1, 
        GO_IL1C1, 
        GO_ML1C1, 
        SnpInvSL1C1, 
        SnpDataL1C1, 
        SnpInvML1C1, 
        GO_WritePullL1C1
      };
      
      ------Backend/Murphi/MurphiModular/Types/Enums/SubEnums/GenArchEnums
      s_directoryL1C1: enum {
        directoryL1C1_dE_RdShared_x_pI_load,
        directoryL1C1_SM_Acks,
        directoryL1C1_S,
        directoryL1C1_M_RdShared_RspSFwdM,
        directoryL1C1_M_RdShared,
        directoryL1C1_M_RdOwn_RspIFwdM,
        directoryL1C1_M_RdOwn,
        directoryL1C1_M_DEvict,
        directoryL1C1_M,
        directoryL1C1_I,
        directoryL1C1_E_RspSFwdM,
        directoryL1C1_E_RdShared,
        directoryL1C1_E_RdOwn_RspIFwdM,
        directoryL1C1_E_RdOwn,
        directoryL1C1_E_DEvict,
        directoryL1C1_E
      };
      
      s_cacheL1C1: enum {
        cacheL1C1_S_store_GO_M,
        cacheL1C1_S_store,
        cacheL1C1_S_evict_SnpInvS,
        cacheL1C1_S_evict,
        cacheL1C1_S,
        cacheL1C1_M_evict_SnpInvM,
        cacheL1C1_M_evict_SnpData_SnpInvS,
        cacheL1C1_M_evict_SnpData,
        cacheL1C1_M_evict,
        cacheL1C1_M,
        cacheL1C1_I_store_GO_M,
        cacheL1C1_I_store_GO_E,
        cacheL1C1_I_store,
        cacheL1C1_I_load_GO_S,
        cacheL1C1_I_load,
        cacheL1C1_I,
        cacheL1C1_E_evict_SnpInvM,
        cacheL1C1_E_evict_SnpData_SnpInvS,
        cacheL1C1_E_evict_SnpData,
        cacheL1C1_E_evict,
        cacheL1C1_E
      };
      
    ----Backend/Murphi/MurphiModular/Types/GenMachineSets
      -- Cluster: C1
      OBJSET_directoryL1C1: enum{directoryL1C1};
      OBJSET_cacheL1C1: scalarset(3);
      C1Machines: union{OBJSET_directoryL1C1, OBJSET_cacheL1C1};
      
      Machines: union{OBJSET_directoryL1C1, OBJSET_cacheL1C1};
    
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
      v_cacheL1C1: multiset[NrCachesL1C1] of Machines;
      cnt_v_cacheL1C1: 0..NrCachesL1C1;
      
      ENTRY_directoryL1C1: record
        State: s_directoryL1C1;
        cl: ClValue;
        acksReceivedL1C1: 0..NrCachesL1C1;
        acksExpectedL1C1: 0..NrCachesL1C1;
        cacheL1C1: v_cacheL1C1;
        ownerL1C1: Machines;
        requesterL1C1: Machines;

        -- [Axiom 1] ordered directory events
        directoryEventFlag : boolean;
      end;
      
      MACH_directoryL1C1: record
        cb: array[Address] of ENTRY_directoryL1C1;
      end;
      
      OBJ_directoryL1C1: array[OBJSET_directoryL1C1] of MACH_directoryL1C1;
      
      ENTRY_cacheL1C1: record
        State: s_cacheL1C1;
        cl: ClValue;
      end;
      
      MACH_cacheL1C1: record
        cb: array[Address] of ENTRY_cacheL1C1;
      end;
      
      OBJ_cacheL1C1: array[OBJSET_cacheL1C1] of MACH_cacheL1C1;
    

  var
    --Backend/Murphi/MurphiModular/GenVars
      D2H_data: NET_Ordered;
      cnt_D2H_data: NET_Ordered_cnt;
      H2D_data: NET_Ordered;
      cnt_H2D_data: NET_Ordered_cnt;
      D2H_request: NET_Unordered;
      D2H_response: NET_Unordered;
      H2D_request: NET_Unordered;
      H2D_response: NET_Unordered;
    
    
      g_perm: PermMonitor;
      i_directoryL1C1: OBJ_directoryL1C1;
      i_cacheL1C1: OBJ_cacheL1C1;
  
--Backend/Murphi/MurphiModular/GenFunctions

  ----Backend/Murphi/MurphiModular/Functions/GenResetFunc
    procedure ResetMachine_directoryL1C1();
    begin
      for i:OBJSET_directoryL1C1 do
        for a:Address do
          i_directoryL1C1[i].cb[a].State := directoryL1C1_I;
          i_directoryL1C1[i].cb[a].cl := 0;
          undefine i_directoryL1C1[i].cb[a].cacheL1C1;
          undefine i_directoryL1C1[i].cb[a].ownerL1C1;
          undefine i_directoryL1C1[i].cb[a].requesterL1C1;
          i_directoryL1C1[i].cb[a].acksReceivedL1C1 := 0;
          i_directoryL1C1[i].cb[a].acksExpectedL1C1 := 0;
    
        endfor;
      endfor;
    end;
    
    procedure ResetMachine_cacheL1C1();
    begin
      for i:OBJSET_cacheL1C1 do
        for a:Address do
          i_cacheL1C1[i].cb[a].State := cacheL1C1_I;
          i_cacheL1C1[i].cb[a].cl := 0;
    
        endfor;
      endfor;
    end;
    
      procedure ResetMachine_();
      begin
      ResetMachine_directoryL1C1();
      ResetMachine_cacheL1C1();
      
      end;
  ----Backend/Murphi/MurphiModular/Functions/GenEventFunc
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
    
  
  ----Backend/Murphi/MurphiModular/Functions/GenVectorFunc
    -- .add()
    procedure AddElement_cacheL1C1(var sv:v_cacheL1C1; n:Machines);
    begin
        if MultiSetCount(i:sv, sv[i] = n) = 0 then
          MultiSetAdd(n, sv);
        endif;
    end;
    
    -- .del()
    procedure RemoveElement_cacheL1C1(var sv:v_cacheL1C1; n:Machines);
    begin
        if MultiSetCount(i:sv, sv[i] = n) = 1 then
          MultiSetRemovePred(i:sv, sv[i] = n);
        endif;
    end;
    
    -- .clear()
    procedure ClearVector_cacheL1C1(var sv:v_cacheL1C1;);
    begin
        MultiSetRemovePred(i:sv, true);
    end;
    
    -- .contains()
    function IsElement_cacheL1C1(var sv:v_cacheL1C1; n:Machines) : boolean;
    begin
        if MultiSetCount(i:sv, sv[i] = n) = 1 then
          return true;
        elsif MultiSetCount(i:sv, sv[i] = n) = 0 then
          return false;
        else
          Error "Multiple Entries of Sharer in SV multiset";
        endif;
      return false;
    end;
    
    -- .empty()
    function HasElement_cacheL1C1(var sv:v_cacheL1C1; n:Machines) : boolean;
    begin
        if MultiSetCount(i:sv, true) = 0 then
          return false;
        endif;
    
        return true;
    end;
    
    -- .count()
    function VectorCount_cacheL1C1(var sv:v_cacheL1C1) : cnt_v_cacheL1C1;
    begin
        return MultiSetCount(i:sv, true);
    end;
    
  ----Backend/Murphi/MurphiModular/Functions/GenFIFOFunc
  ----Backend/Murphi/MurphiModular/Functions/GenNetworkFunc
    procedure Send_D2H_data(msg:Message; src: Machines;);
      Assert(cnt_D2H_data[msg.dst] < O_NET_MAX) "Too many messages";
      D2H_data[msg.dst][cnt_D2H_data[msg.dst]] := msg;
      cnt_D2H_data[msg.dst] := cnt_D2H_data[msg.dst] + 1;
    end;
    
    procedure Pop_D2H_data(dst:Machines; src: Machines;);
    begin
      Assert (cnt_D2H_data[dst] > 0) "Trying to advance empty Q";
      for i := 0 to cnt_D2H_data[dst]-1 do
        if i < cnt_D2H_data[dst]-1 then
          D2H_data[dst][i] := D2H_data[dst][i+1];
        else
          undefine D2H_data[dst][i];
        endif;
      endfor;
      cnt_D2H_data[dst] := cnt_D2H_data[dst] - 1;
    end;
    
    procedure Send_H2D_data(msg:Message; src: Machines;);
      Assert(cnt_H2D_data[msg.dst] < O_NET_MAX) "Too many messages";
      H2D_data[msg.dst][cnt_H2D_data[msg.dst]] := msg;
      cnt_H2D_data[msg.dst] := cnt_H2D_data[msg.dst] + 1;
    end;
    
    procedure Pop_H2D_data(dst:Machines; src: Machines;);
    begin
      Assert (cnt_H2D_data[dst] > 0) "Trying to advance empty Q";
      for i := 0 to cnt_H2D_data[dst]-1 do
        if i < cnt_H2D_data[dst]-1 then
          H2D_data[dst][i] := H2D_data[dst][i+1];
        else
          undefine H2D_data[dst][i];
        endif;
      endfor;
      cnt_H2D_data[dst] := cnt_H2D_data[dst] - 1;
    end;
    
    procedure Send_D2H_request(msg:Message; src: Machines;);
      Assert (MultiSetCount(i:D2H_request[msg.dst], true) < U_NET_MAX) "Too many messages";
      MultiSetAdd(msg, D2H_request[msg.dst]);
    end;
    
    procedure Send_D2H_response(msg:Message; src: Machines;);
      Assert (MultiSetCount(i:D2H_response[msg.dst], true) < U_NET_MAX) "Too many messages";
      MultiSetAdd(msg, D2H_response[msg.dst]);
    end;
    
    procedure Send_H2D_request(msg:Message; src: Machines;);
      Assert (MultiSetCount(i:H2D_request[msg.dst], true) < U_NET_MAX) "Too many messages";
      MultiSetAdd(msg, H2D_request[msg.dst]);
    end;
    
    procedure Send_H2D_response(msg:Message; src: Machines;);
      Assert (MultiSetCount(i:H2D_response[msg.dst], true) < U_NET_MAX) "Too many messages";
      MultiSetAdd(msg, H2D_response[msg.dst]);
    end;
    
    procedure Multicast_H2D_request_v_cacheL1C1(var msg: Message; dst_vect: v_cacheL1C1; src: Machines;);
    begin
          for n:Machines do
              if n!=msg.src then
                if MultiSetCount(i:dst_vect, dst_vect[i] = n) = 1 then
                  msg.dst := n;
                  Send_H2D_request(msg, src);
                endif;
              endif;
          endfor;
    end;
    
    function D2H_data_network_ready(): boolean;
    begin
          for dst:Machines do
            for src: Machines do
              if cnt_D2H_data[dst] >= (O_NET_MAX-5) then
                return false;
              endif;
            endfor;
          endfor;
    
          return true;
    end;
    function D2H_response_network_ready(): boolean;
    begin
          for mach:Machines do
            alias mul_set:D2H_response[mach] do
              if MultisetCount(i:mul_set, isundefined(mul_set[i].mtype)) >= (U_NET_MAX-5) then
                return false;
              endif;
            endalias;
          endfor;
    
          return true;
    end;
    function H2D_response_network_ready(): boolean;
    begin
          for mach:Machines do
            alias mul_set:H2D_response[mach] do
              if MultisetCount(i:mul_set, isundefined(mul_set[i].mtype)) >= (U_NET_MAX-5) then
                return false;
              endif;
            endalias;
          endfor;
    
          return true;
    end;
    function H2D_data_network_ready(): boolean;
    begin
          for dst:Machines do
            for src: Machines do
              if cnt_H2D_data[dst] >= (O_NET_MAX-5) then
                return false;
              endif;
            endfor;
          endfor;
    
          return true;
    end;
    function H2D_request_network_ready(): boolean;
    begin
          for mach:Machines do
            alias mul_set:H2D_request[mach] do
              if MultisetCount(i:mul_set, isundefined(mul_set[i].mtype)) >= (U_NET_MAX-5) then
                return false;
              endif;
            endalias;
          endfor;
    
          return true;
    end;
    function D2H_request_network_ready(): boolean;
    begin
          for mach:Machines do
            alias mul_set:D2H_request[mach] do
              if MultisetCount(i:mul_set, isundefined(mul_set[i].mtype)) >= (U_NET_MAX-5) then
                return false;
              endif;
            endalias;
          endfor;
    
          return true;
    end;
    function network_ready(): boolean;
    begin
            if !D2H_data_network_ready() then
            return false;
          endif;
    
    
          if !D2H_response_network_ready() then
            return false;
          endif;
    
    
          if !H2D_response_network_ready() then
            return false;
          endif;
    
    
          if !H2D_data_network_ready() then
            return false;
          endif;
    
    
          if !H2D_request_network_ready() then
            return false;
          endif;
    
    
          if !D2H_request_network_ready() then
            return false;
          endif;
    
    
    
      return true;
    end;
    
    procedure Reset_NET_();
    begin
      
      undefine H2D_data;
      for dst:Machines do
          cnt_H2D_data[dst] := 0;
      endfor;
      
      undefine D2H_data;
      for dst:Machines do
          cnt_D2H_data[dst] := 0;
      endfor;
      
      undefine D2H_response;
      
      undefine H2D_response;
      
      undefine H2D_request;
      
      undefine D2H_request;
    
    end;
    
  
  ----Backend/Murphi/MurphiModular/Functions/GenMessageConstrFunc
    function DevReqL1C1(adr: Address; mtype: MessageType; src: Machines; dst: Machines) : Message;
    var Message: Message;
    begin
      Message.adr := adr;
      Message.mtype := mtype;
      Message.src := src;
      Message.dst := dst;
    return Message;
    end;
    
    function DevRspL1C1(adr: Address; mtype: MessageType; src: Machines; dst: Machines) : Message;
    var Message: Message;
    begin
      Message.adr := adr;
      Message.mtype := mtype;
      Message.src := src;
      Message.dst := dst;
    return Message;
    end;
    
    function DataFullL1C1(adr: Address; mtype: MessageType; src: Machines; dst: Machines; cl: ClValue) : Message;
    var Message: Message;
    begin
      Message.adr := adr;
      Message.mtype := mtype;
      Message.src := src;
      Message.dst := dst;
      Message.cl := cl;
    return Message;
    end;
    
    function HostReqL1C1(adr: Address; mtype: MessageType; src: Machines; dst: Machines) : Message;
    var Message: Message;
    begin
      Message.adr := adr;
      Message.mtype := mtype;
      Message.src := src;
      Message.dst := dst;
    return Message;
    end;
    
    function HostRspL1C1(adr: Address; mtype: MessageType; src: Machines; dst: Machines) : Message;
    var Message: Message;
    begin
      Message.adr := adr;
      Message.mtype := mtype;
      Message.src := src;
      Message.dst := dst;
    return Message;
    end;
    
  

--Backend/Murphi/MurphiModular/GenStateMachines

  ----Backend/Murphi/MurphiModular/StateMachines/GenAccessStateMachines
    procedure FSM_Access_cacheL1C1_E_evict(adr:Address; m:OBJSET_cacheL1C1);
    var msg: Message;
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      msg := DevReqL1C1(adr, CleanEvictNoDataL1C1, m, directoryL1C1);
      Send_D2H_request(msg, m);
      cbe.State := cacheL1C1_E_evict;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_E_load(adr:Address; m:OBJSET_cacheL1C1);
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      cbe.State := cacheL1C1_E;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_E_store(adr:Address; m:OBJSET_cacheL1C1);
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      cbe.State := cacheL1C1_M;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_I_evict(adr:Address; m:OBJSET_cacheL1C1);
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      cbe.State := cacheL1C1_I;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_I_load(adr:Address; m:OBJSET_cacheL1C1);
    var msg: Message;
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      msg := DevReqL1C1(adr, RdSharedL1C1, m, directoryL1C1);
      Send_D2H_request(msg, m);
      cbe.State := cacheL1C1_I_load;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_I_store(adr:Address; m:OBJSET_cacheL1C1);
    var msg: Message;
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      msg := DevReqL1C1(adr, RdOwnL1C1, m, directoryL1C1);
      Send_D2H_request(msg, m);
      cbe.State := cacheL1C1_I_store;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_M_evict(adr:Address; m:OBJSET_cacheL1C1);
    var msg: Message;
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      msg := DevReqL1C1(adr, DirtyEvictL1C1, m, directoryL1C1);
      Send_D2H_request(msg, m);
      cbe.State := cacheL1C1_M_evict;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_M_load(adr:Address; m:OBJSET_cacheL1C1);
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      cbe.State := cacheL1C1_M;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_M_store(adr:Address; m:OBJSET_cacheL1C1);
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      cbe.State := cacheL1C1_M;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_S_evict(adr:Address; m:OBJSET_cacheL1C1);
    var msg: Message;
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      msg := DevReqL1C1(adr, CleanEvictNoDataL1C1, m, directoryL1C1);
      Send_D2H_request(msg, m);
      cbe.State := cacheL1C1_S_evict;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_S_load(adr:Address; m:OBJSET_cacheL1C1);
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      cbe.State := cacheL1C1_S;
    endalias;
    end;
    
    procedure FSM_Access_cacheL1C1_S_store(adr:Address; m:OBJSET_cacheL1C1);
    var msg: Message;
    begin
    alias cbe: i_cacheL1C1[m].cb[adr] do
      msg := DevReqL1C1(adr, RdOwnL1C1, m, directoryL1C1);
      Send_D2H_request(msg, m);
      cbe.State := cacheL1C1_S_store;
    endalias;
    end;
    
    procedure FSM_Access_directoryL1C1_S_store(adr:Address; m:OBJSET_directoryL1C1);
    var inmsg: Message;
    var msg: Message;
    var msg1: Message;
    begin
    alias cbe: i_directoryL1C1[m].cb[adr] do
      inmsg := DevReqL1C1(adr, RdOwnL1C1, m, m);
      Clear_perm(adr, m);
      -- cbe.State := directoryL1C1_M_RdOwn;
      -- cbe.State := directoryL1C1_dE_RdOwn_x_pI_store;

      cbe.ownerL1C1 := inmsg.src;
      cbe.acksExpectedL1C1 := VectorCount_cacheL1C1(cbe.cacheL1C1);
      if !(IsElement_cacheL1C1(cbe.cacheL1C1, inmsg.src)) then
        if (IsElement_cacheL1C1(cbe.cacheL1C1, inmsg.dst)) then
          cbe.acksExpectedL1C1 := cbe.acksExpectedL1C1-1;
          cbe.acksReceivedL1C1 := 0;
          if !(cbe.acksExpectedL1C1 != 0) then
            msg := HostRspL1C1(adr,GO_ML1C1,m,cbe.ownerL1C1);
            Send_H2D_response(msg, m);
            msg1 := DataFullL1C1(adr,HostDataMsgL1C1,m,inmsg.src,cbe.cl);
            Send_H2D_data(msg1, m);
            if !(IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
              Clear_perm(adr, m);
              cbe.State := directoryL1C1_I;
              -- cbe.State := directoryL1C1_M;
              -- return true;

              -- [Axiom 1]
              assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
              -- cbe.directoryEventFlag := true;

            endif;
            if (IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
              ClearVector_cacheL1C1(cbe.cacheL1C1);
              Clear_perm(adr, m);
              cbe.State := directoryL1C1_I;
              -- cbe.State := directoryL1C1_M;
              -- return true;

              -- [Axiom 1]
              assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
              -- cbe.directoryEventFlag := true;

            endif;
          endif;
          if (cbe.acksExpectedL1C1 != 0) then
            if !(IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
              msg := HostReqL1C1(adr,SnpInvSL1C1,m,m);
              Multicast_H2D_request_v_cacheL1C1(msg, cbe.cacheL1C1, m);
              ClearVector_cacheL1C1(cbe.cacheL1C1);
              Clear_perm(adr, m);
              cbe.State := directoryL1C1_SM_Acks;
              -- return true;

              -- [Axiom 1]
              assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
              cbe.directoryEventFlag := true;

            endif;
            if (IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
              RemoveElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1);
              msg := HostReqL1C1(adr,SnpInvSL1C1,m,m);
              Multicast_H2D_request_v_cacheL1C1(msg, cbe.cacheL1C1, m);
              ClearVector_cacheL1C1(cbe.cacheL1C1);
              AddElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1);
              Clear_perm(adr, m);
              cbe.State := directoryL1C1_SM_Acks;
              -- return true;

              -- [Axiom 1]
              assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
              cbe.directoryEventFlag := true;

            endif;
          endif;
        endif;
        if !(IsElement_cacheL1C1(cbe.cacheL1C1, inmsg.dst)) then
          cbe.acksReceivedL1C1 := 0;
          if (cbe.acksExpectedL1C1 != 0) then
            if (IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
              RemoveElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1);
              msg := HostReqL1C1(adr,SnpInvSL1C1,m,m);
              Multicast_H2D_request_v_cacheL1C1(msg, cbe.cacheL1C1, m);
              ClearVector_cacheL1C1(cbe.cacheL1C1);
              AddElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1);
              Clear_perm(adr, m);
              cbe.State := directoryL1C1_SM_Acks;
              -- return true;

              -- [Axiom 1]
              assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
              cbe.directoryEventFlag := true;

            endif;
            if !(IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
              msg := HostReqL1C1(adr,SnpInvSL1C1,m,m);
              Multicast_H2D_request_v_cacheL1C1(msg, cbe.cacheL1C1, m);
              ClearVector_cacheL1C1(cbe.cacheL1C1);
              Clear_perm(adr, m);
              cbe.State := directoryL1C1_SM_Acks;
              -- return true;

              -- [Axiom 1]
              assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
              cbe.directoryEventFlag := true;

            endif;
          endif;
          if !(cbe.acksExpectedL1C1 != 0) then
            msg := HostRspL1C1(adr,GO_ML1C1,m,cbe.ownerL1C1);
            Send_H2D_response(msg, m);
            msg1 := DataFullL1C1(adr,HostDataMsgL1C1,m,inmsg.src,cbe.cl);
            Send_H2D_data(msg1, m);
            if (IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
              ClearVector_cacheL1C1(cbe.cacheL1C1);
              Clear_perm(adr, m);
              cbe.State := directoryL1C1_I;
              -- cbe.State := directoryL1C1_M;
              -- return true;

              -- [Axiom 1]
              assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
              -- cbe.directoryEventFlag := true;

            endif;
            if !(IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
              Clear_perm(adr, m);
              cbe.State := directoryL1C1_I;
              -- cbe.State := directoryL1C1_M;
              -- return true;

              -- [Axiom 1]
              assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
              -- cbe.directoryEventFlag := true;

            endif;
          endif;
        endif;
      endif;
      if (IsElement_cacheL1C1(cbe.cacheL1C1, inmsg.src)) then
        cbe.acksExpectedL1C1 := cbe.acksExpectedL1C1-1;
        if (IsElement_cacheL1C1(cbe.cacheL1C1, inmsg.dst)) then
          cbe.acksExpectedL1C1 := cbe.acksExpectedL1C1-1;
          cbe.acksReceivedL1C1 := 0;
          if !(cbe.acksExpectedL1C1 != 0) then
            msg := HostRspL1C1(adr,GO_ML1C1,m,cbe.ownerL1C1);
            Send_H2D_response(msg, m);
            msg1 := DataFullL1C1(adr,HostDataMsgL1C1,m,inmsg.src,cbe.cl);
            Send_H2D_data(msg1, m);
            if !(IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
              Clear_perm(adr, m);
              cbe.State := directoryL1C1_I;
              -- cbe.State := directoryL1C1_M;
              -- return true;

              -- [Axiom 1]
              assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
              -- cbe.directoryEventFlag := true;

            endif;
            if (IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
              ClearVector_cacheL1C1(cbe.cacheL1C1);
              Clear_perm(adr, m);
              cbe.State := directoryL1C1_I;
              -- cbe.State := directoryL1C1_M;
              -- return true;

              -- [Axiom 1]
              assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
              -- cbe.directoryEventFlag := true;

            endif;
          endif;
          if (cbe.acksExpectedL1C1 != 0) then
            if (IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
              RemoveElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1);
              msg := HostReqL1C1(adr,SnpInvSL1C1,m,m);
              Multicast_H2D_request_v_cacheL1C1(msg, cbe.cacheL1C1, m);
              ClearVector_cacheL1C1(cbe.cacheL1C1);
              AddElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1);
              Clear_perm(adr, m);
              cbe.State := directoryL1C1_SM_Acks;
              -- return true;

              -- [Axiom 1]
              assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
              cbe.directoryEventFlag := true;

            endif;
            if !(IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
              msg := HostReqL1C1(adr,SnpInvSL1C1,m,m);
              Multicast_H2D_request_v_cacheL1C1(msg, cbe.cacheL1C1, m);
              ClearVector_cacheL1C1(cbe.cacheL1C1);
              Clear_perm(adr, m);
              cbe.State := directoryL1C1_SM_Acks;
              -- return true;

              -- [Axiom 1]
              assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
              cbe.directoryEventFlag := true;

            endif;
          endif;
        endif;
        if !(IsElement_cacheL1C1(cbe.cacheL1C1, inmsg.dst)) then
          cbe.acksReceivedL1C1 := 0;
          if (cbe.acksExpectedL1C1 != 0) then
            if !(IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
              msg := HostReqL1C1(adr,SnpInvSL1C1,m,m);
              Multicast_H2D_request_v_cacheL1C1(msg, cbe.cacheL1C1, m);
              ClearVector_cacheL1C1(cbe.cacheL1C1);
              Clear_perm(adr, m);
              cbe.State := directoryL1C1_SM_Acks;
              -- return true;

              -- [Axiom 1]
              assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
              -- cbe.directoryEventFlag := true;

            endif;
            if (IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
              RemoveElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1);
              msg := HostReqL1C1(adr,SnpInvSL1C1,m,m);
              Multicast_H2D_request_v_cacheL1C1(msg, cbe.cacheL1C1, m);
              ClearVector_cacheL1C1(cbe.cacheL1C1);
              AddElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1);
              Clear_perm(adr, m);
              cbe.State := directoryL1C1_SM_Acks;
              -- return true;

              -- [Axiom 1]
              assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
              -- cbe.directoryEventFlag := true;

            endif;
          endif;
          if !(cbe.acksExpectedL1C1 != 0) then
            msg := HostRspL1C1(adr,GO_ML1C1,m,cbe.ownerL1C1);
            Send_H2D_response(msg, m);
            msg1 := DataFullL1C1(adr,HostDataMsgL1C1,m,inmsg.src,cbe.cl);
            Send_H2D_data(msg1, m);
            if !(IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
              Clear_perm(adr, m);
              cbe.State := directoryL1C1_I;
              -- cbe.State := directoryL1C1_M;
              -- return true;

              -- [Axiom 1]
              assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
              -- cbe.directoryEventFlag := true;

            endif;
            if (IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
              ClearVector_cacheL1C1(cbe.cacheL1C1);
              Clear_perm(adr, m);
              cbe.State := directoryL1C1_I;
              -- cbe.State := directoryL1C1_M;
              -- return true;

              -- [Axiom 1]
              assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
              -- cbe.directoryEventFlag := true;

            endif;
          endif;
        endif;
      endif;
    endalias;
    end;
    
    procedure FSM_Access_directoryL1C1_M_load(adr:Address; m:OBJSET_directoryL1C1);
    var msg_RdSharedL1: Message;
    var msg: Message;
    begin
    alias cbe: i_directoryL1C1[m].cb[adr] do
      msg_RdSharedL1 := DevReqL1C1(adr, RdSharedL1C1, m, m);
      msg := HostReqL1C1(adr, SnpDataL1C1, msg_RdSharedL1.src, cbe.ownerL1C1);
      Send_H2D_request(msg, m);
      AddElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1);
      if !(msg_RdSharedL1.src != m) then
      cbe.requesterL1C1 := msg_RdSharedL1.src;
      cbe.State := directoryL1C1_M_RdShared;
      -- cbe.State := directoryL1C1_dE_RdShared_x_pI_load;
      endif
    endalias;
    end;
    
    procedure FSM_Access_directoryL1C1_M_store(adr:Address; m:OBJSET_directoryL1C1);
    var msg_RdOwnL1: Message;
    var msg: Message;
    begin
    alias cbe: i_directoryL1C1[m].cb[adr] do
      msg_RdOwnL1 := DevReqL1C1(adr, RdOwnL1C1, m, m);
      msg := HostReqL1C1(adr, SnpInvML1C1, msg_RdOwnL1.src, cbe.ownerL1C1);
      Send_H2D_request(msg, m);
      cbe.ownerL1C1 := msg_RdOwnL1.src;
      Clear_perm(adr, m);
      cbe.State := directoryL1C1_M_RdOwn;
      -- cbe.State := directoryL1C1_dE_RdOwn_x_pI_store;
    endalias;
    end;
    
    procedure FSM_Access_directoryL1C1_E_load(adr:Address; m:OBJSET_directoryL1C1);
    var msg_RdSharedL1: Message;
    var msg: Message;
    begin
    alias cbe: i_directoryL1C1[m].cb[adr] do
      msg_RdSharedL1 := DevReqL1C1(adr, RdSharedL1C1, m, m);
      msg := HostReqL1C1(adr, SnpDataL1C1, msg_RdSharedL1.src, cbe.ownerL1C1);
      Send_H2D_request(msg, m);
      AddElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1);
      if !(msg_RdSharedL1.src != m) then
      cbe.requesterL1C1 := msg_RdSharedL1.src;
      cbe.State := directoryL1C1_E_RdShared;
      -- cbe.State := directoryL1C1_dE_RdShared_x_pI_load;
      endif
    endalias;
    end;
    
    procedure FSM_Access_directoryL1C1_E_store(adr:Address; m:OBJSET_directoryL1C1);
    var msg_RdOwnL1: Message;
    var msg: Message;
    begin
    alias cbe: i_directoryL1C1[m].cb[adr] do
      msg_RdOwnL1 := DevReqL1C1(adr, RdOwnL1C1, m, m);
      msg := HostReqL1C1(adr, SnpInvML1C1, msg_RdOwnL1.src, cbe.ownerL1C1);
      Send_H2D_request(msg, m);
      cbe.ownerL1C1 := msg_RdOwnL1.src;
      Clear_perm(adr, m);
      cbe.State := directoryL1C1_E_RdOwn;
      -- cbe.State := directoryL1C1_dE_RdOwn_x_pI_store;
    endalias;
    end;
    
    procedure FSM_Access_directoryL1C1_I_load(adr:Address; m:OBJSET_directoryL1C1);
    var msg_RdSharedL1: Message;
    var msg_GO_SL1: Message;
    var msg1_HostDataMsgL1: Message;
    var msg_CleanEvictNoDataL1: Message;
    var msg_GO_IL1: Message;
    begin
    alias cbe: i_directoryL1C1[m].cb[adr] do
      msg_RdSharedL1 := DevReqL1C1(adr, RdSharedL1C1, m, m);
      AddElement_cacheL1C1(cbe.cacheL1C1, msg_RdSharedL1.src);
      msg_GO_SL1 := HostRspL1C1(adr, GO_SL1C1, m, msg_RdSharedL1.src);
      msg1_HostDataMsgL1 := DataFullL1C1(adr, HostDataMsgL1C1, m, msg_RdSharedL1.src, cbe.cl);
      cbe.cl := msg1_HostDataMsgL1.cl;
      msg_CleanEvictNoDataL1 := DevReqL1C1(adr, CleanEvictNoDataL1C1, m, m);
      msg_GO_IL1 := HostRspL1C1(adr, GO_IL1C1, m, msg_CleanEvictNoDataL1.src);
      if (IsElement_cacheL1C1(cbe.cacheL1C1, msg_CleanEvictNoDataL1.src)  ) then
      if !(VectorCount_cacheL1C1(cbe.cacheL1C1) = 1) then
      RemoveElement_cacheL1C1(cbe.cacheL1C1, msg_CleanEvictNoDataL1.src);
      cbe.State := directoryL1C1_S;
      endif
      endif
    endalias;
    end;
    
    procedure FSM_Access_directoryL1C1_I_store(adr:Address; m:OBJSET_directoryL1C1);
    var msg_RdOwnL1: Message;
    var msg_GO_EL1: Message;
    var msg1_HostDataMsgL1: Message;
    var msg_CleanEvictNoDataL1: Message;
    var msg_GO_IL1: Message;
    begin
    alias cbe: i_directoryL1C1[m].cb[adr] do
      msg_RdOwnL1 := DevReqL1C1(adr, RdOwnL1C1, m, m);
      cbe.ownerL1C1 := msg_RdOwnL1.src;
      msg_GO_EL1 := HostRspL1C1(adr, GO_EL1C1, m, msg_RdOwnL1.src);
      msg1_HostDataMsgL1 := DataFullL1C1(adr, HostDataMsgL1C1, m, msg_RdOwnL1.src, cbe.cl);
      cbe.cl := msg1_HostDataMsgL1.cl;
      msg_CleanEvictNoDataL1 := DevReqL1C1(adr, CleanEvictNoDataL1C1, m, m);
      msg_GO_IL1 := HostRspL1C1(adr, GO_IL1C1, m, msg_CleanEvictNoDataL1.src);
      if (msg_CleanEvictNoDataL1.src = cbe.ownerL1C1) then
      cbe.State := directoryL1C1_I;
      endif
    endalias;
    end;
    
    procedure FSM_Access_directoryL1C1_S_load(adr:Address; m:OBJSET_directoryL1C1);
    var msg_RdSharedL1: Message;
    var msg_GO_SL1: Message;
    var msg1_HostDataMsgL1: Message;
    var msg_CleanEvictNoDataL1: Message;
    var msg_GO_IL1: Message;
    begin
    alias cbe: i_directoryL1C1[m].cb[adr] do
      msg_RdSharedL1 := DevReqL1C1(adr, RdSharedL1C1, m, m);
      msg_GO_SL1 := HostRspL1C1(adr, GO_SL1C1, m, msg_RdSharedL1.src);
      msg1_HostDataMsgL1 := DataFullL1C1(adr, HostDataMsgL1C1, m, msg_RdSharedL1.src, cbe.cl);
      AddElement_cacheL1C1(cbe.cacheL1C1, msg_RdSharedL1.src);
      cbe.cl := msg1_HostDataMsgL1.cl;
      msg_CleanEvictNoDataL1 := DevReqL1C1(adr, CleanEvictNoDataL1C1, m, m);
      msg_GO_IL1 := HostRspL1C1(adr, GO_IL1C1, m, msg_CleanEvictNoDataL1.src);
      if (IsElement_cacheL1C1(cbe.cacheL1C1, msg_CleanEvictNoDataL1.src)  ) then
      if (VectorCount_cacheL1C1(cbe.cacheL1C1) = 1) then
      RemoveElement_cacheL1C1(cbe.cacheL1C1, msg_CleanEvictNoDataL1.src);
      cbe.State := directoryL1C1_I;
      endif
      endif
    endalias;
    end;
    
  ----Backend/Murphi/MurphiModular/StateMachines/GenMessageStateMachines
    function FSM_MSG_directoryL1C1(inmsg:Message; m:OBJSET_directoryL1C1) : boolean;
    var msg: Message;
    var msg1: Message;
    var msg2: Message;
    var msg1_GO_SL1: Message;
    var msg2_HostDataMsgL1: Message;
    var msg_CleanEvictNoDataL1: Message;
    var msg_GO_IL1: Message;
    begin
      alias adr: inmsg.adr do
      alias cbe: i_directoryL1C1[m].cb[adr] do
    switch cbe.State
      case directoryL1C1_E:
      switch inmsg.mtype
        case CleanEvictNoDataL1C1:
          -- [Axiom 1]
          assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";

          msg := HostRspL1C1(adr,GO_IL1C1,m,inmsg.src);
          Send_H2D_response(msg, m);
          if !(inmsg.src = cbe.ownerL1C1) then
            Clear_perm(adr, m);
            cbe.State := directoryL1C1_E;
            undefine cbe.requesterL1C1;
            return true;
          endif;
          if (inmsg.src = cbe.ownerL1C1) then
            Clear_perm(adr, m);
            cbe.State := directoryL1C1_I;
            undefine cbe.requesterL1C1;
            return true;
          endif;
        
        case DirtyEvictL1C1:
          if (inmsg.src = cbe.ownerL1C1) then
            -- [Axiom 1]
            assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
            cbe.directoryEventFlag := true;

            msg := HostRspL1C1(adr,GO_WritePullL1C1,m,inmsg.src);
            Send_H2D_response(msg, m);
            Clear_perm(adr, m);
            cbe.State := directoryL1C1_E_DEvict;
            return true;
          endif;
          if !(inmsg.src = cbe.ownerL1C1) then
            -- [Axiom 1]
            assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";

            msg := HostRspL1C1(adr,GO_IL1C1,m,inmsg.src);
            Send_H2D_response(msg, m);
            Clear_perm(adr, m);
            cbe.State := directoryL1C1_E;
            undefine cbe.requesterL1C1;
            return true;
          endif;
        
        case RdOwnL1C1:
          -- [Axiom 1]
          assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
          cbe.directoryEventFlag := true;

          msg := HostReqL1C1(adr,SnpInvML1C1,inmsg.src,cbe.ownerL1C1);
          Send_H2D_request(msg, m);
          cbe.ownerL1C1 := inmsg.src;
          Clear_perm(adr, m);
          cbe.State := directoryL1C1_E_RdOwn;
          return true;
        
        case RdSharedL1C1:
          -- [Axiom 1]
          assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
          cbe.directoryEventFlag := true;

          msg := HostReqL1C1(adr,SnpDataL1C1,inmsg.src,cbe.ownerL1C1);
          Send_H2D_request(msg, m);
          AddElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1);
          if !(inmsg.src != m) then
            cbe.requesterL1C1 := inmsg.src;
            Clear_perm(adr, m);
            cbe.State := directoryL1C1_E_RdShared;
            return true;
          endif;
          if (inmsg.src != m) then
            AddElement_cacheL1C1(cbe.cacheL1C1, inmsg.src);
            cbe.requesterL1C1 := inmsg.src;
            Clear_perm(adr, m);
            cbe.State := directoryL1C1_E_RdShared;
            return true;
          endif;
        
        else return false;
      endswitch;
      
      case directoryL1C1_E_DEvict:
      switch inmsg.mtype
        case DevDataMsgL1C1:
          -- [Axiom 1]
          assert !isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory ending an event. Why is the directoryEventFlag not set?\n";
          undefine cbe.directoryEventFlag;

          cbe.cl := inmsg.cl;
          Clear_perm(adr, m);
          cbe.State := directoryL1C1_I;
          undefine cbe.requesterL1C1;
          return true;
        
        else return false;
      endswitch;
      
      case directoryL1C1_E_RdOwn:
      switch inmsg.mtype
        case RspIFwdML1C1:
          Clear_perm(adr, m);
          cbe.State := directoryL1C1_E_RdOwn_RspIFwdM;
          return true;
        
        case RspIHitSEL1C1:
          if (cbe.ownerL1C1 != directoryL1C1) then
            msg1 := HostRspL1C1(adr,GO_ML1C1,m,inmsg.src);
            Send_H2D_response(msg1, m);
            msg2 := DataFullL1C1(adr,HostDataMsgL1C1,m,inmsg.src,cbe.cl);
            Send_H2D_data(msg2, m);
            Clear_perm(adr, m);
            cbe.State := directoryL1C1_M;
            undefine cbe.requesterL1C1;
          else
            Clear_perm(adr, m);
            cbe.State := directoryL1C1_I;
            undefine cbe.requesterL1C1;
          endif;

          -- [Axiom 1]
          assert !isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory ending an event. Why is the directoryEventFlag not set?\n";
          undefine cbe.directoryEventFlag;

          return true;
        
        else return false;
      endswitch;
      
      case directoryL1C1_E_RdOwn_RspIFwdM:
      switch inmsg.mtype
        case DevDataMsgL1C1:
          if (cbe.ownerL1C1 != directoryL1C1) then
            cbe.cl := inmsg.cl;
            msg1 := HostRspL1C1(adr,GO_ML1C1,m,cbe.ownerL1C1);
            Send_H2D_response(msg1, m);
            msg2 := DataFullL1C1(adr,HostDataMsgL1C1,m,cbe.ownerL1C1,inmsg.cl);
            Send_H2D_data(msg2, m);
            Clear_perm(adr, m);
            cbe.State := directoryL1C1_M;
            undefine cbe.requesterL1C1;
          else
            Clear_perm(adr, m);
            cbe.State := directoryL1C1_I;
            undefine cbe.requesterL1C1;
          endif;

          -- [Axiom 1]
          assert !isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory ending an event. Why is the directoryEventFlag not set?\n";
          undefine cbe.directoryEventFlag;

          return true;
        
        else return false;
      endswitch;
      
      case directoryL1C1_E_RdShared:
      switch inmsg.mtype
        case RspSFwdML1C1:
          Clear_perm(adr, m);
          cbe.State := directoryL1C1_E_RspSFwdM;
          return true;
        
        case RspSHitSEL1C1:
          if (inmsg.src != directoryL1C1) then
            msg1 := HostRspL1C1(adr,GO_SL1C1,m,inmsg.src);
            Send_H2D_response(msg1, m);
            msg2 := DataFullL1C1(adr,HostDataMsgL1C1,m,inmsg.src,cbe.cl);
            Send_H2D_data(msg2, m);
          endif;
          Clear_perm(adr, m);
          cbe.State := directoryL1C1_S;
          undefine cbe.requesterL1C1;

          -- [Axiom 1]
          assert !isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory ending an event. Why is the directoryEventFlag not set?\n";
          undefine cbe.directoryEventFlag;

          return true;
        
        else return false;
      endswitch;
      
      case directoryL1C1_E_RspSFwdM:
      switch inmsg.mtype
        case DevDataMsgL1C1:

          -- [Axiom 1]
          assert !isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory ending an event. Why is the directoryEventFlag not set?\n";
          undefine cbe.directoryEventFlag;

          if (cbe.requesterL1C1 != m) then
            msg1 := HostRspL1C1(adr,GO_SL1C1,m,cbe.requesterL1C1);
            Send_H2D_response(msg1, m);
            cbe.cl := inmsg.cl;
            msg2 := DataFullL1C1(adr,HostDataMsgL1C1,m,cbe.requesterL1C1,inmsg.cl);
            Send_H2D_data(msg2, m);
            Clear_perm(adr, m);
            cbe.State := directoryL1C1_S;
            undefine cbe.requesterL1C1;
            return true;
          endif;
          if !(cbe.requesterL1C1 != m) then
            Clear_perm(adr, m);
            cbe.State := directoryL1C1_S;
            return true;
            undefine cbe.requesterL1C1;
          endif;
        
        else return false;
      endswitch;
      
      case directoryL1C1_I:
      switch inmsg.mtype
        case CleanEvictNoDataL1C1:
          msg := HostRspL1C1(adr,GO_IL1C1,m,inmsg.src);
          Send_H2D_response(msg, m);
          Clear_perm(adr, m);
          cbe.State := directoryL1C1_I;
          undefine cbe.requesterL1C1;

          -- [Axiom 1]
          assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
          -- cbe.directoryEventFlag := true;

          return true;
        
        case DirtyEvictL1C1:
          msg := HostRspL1C1(adr,GO_IL1C1,m,inmsg.src);
          Send_H2D_response(msg, m);
          Clear_perm(adr, m);
          cbe.State := directoryL1C1_I;
          undefine cbe.requesterL1C1;

          -- [Axiom 1]
          assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
          -- cbe.directoryEventFlag := true;

          return true;
        
        case RdOwnL1C1:
          cbe.ownerL1C1 := inmsg.src;
          msg := HostRspL1C1(adr,GO_EL1C1,m,inmsg.src);
          Send_H2D_response(msg, m);
          msg1 := DataFullL1C1(adr,HostDataMsgL1C1,m,inmsg.src,cbe.cl);
          Send_H2D_data(msg1, m);
          Clear_perm(adr, m);
          cbe.State := directoryL1C1_E;
          undefine cbe.requesterL1C1;

          -- [Axiom 1]
          assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
          -- cbe.directoryEventFlag := true;

          return true;
        
        case RdSharedL1C1:
          AddElement_cacheL1C1(cbe.cacheL1C1, inmsg.src);
          msg := HostRspL1C1(adr,GO_SL1C1,m,inmsg.src);
          Send_H2D_response(msg, m);
          msg1 := DataFullL1C1(adr,HostDataMsgL1C1,m,inmsg.src,cbe.cl);
          Send_H2D_data(msg1, m);
          Clear_perm(adr, m);
          cbe.State := directoryL1C1_S;
          undefine cbe.requesterL1C1;

          -- [Axiom 1]
          assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
          -- cbe.directoryEventFlag := true;

          return true;
        
        else return false;
      endswitch;
      
      case directoryL1C1_M:
      switch inmsg.mtype
        case CleanEvictNoDataL1C1:
          -- [Axiom 1]
          assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
          -- cbe.directoryEventFlag := true;

          if (inmsg.src != cbe.ownerL1C1) then
            msg := HostRspL1C1(adr,GO_IL1C1,m,inmsg.src);
            Send_H2D_response(msg, m);
            Clear_perm(adr, m);
            cbe.State := directoryL1C1_M;
            undefine cbe.requesterL1C1;
            return true;
          endif;
          if !(inmsg.src != cbe.ownerL1C1) then
            Clear_perm(adr, m);
            cbe.State := directoryL1C1_M;
            undefine cbe.requesterL1C1;
            return true;
          endif;
        
        case DirtyEvictL1C1:
          if !(inmsg.src = cbe.ownerL1C1) then
            msg := HostRspL1C1(adr,GO_IL1C1,m,inmsg.src);
            Send_H2D_response(msg, m);
            Clear_perm(adr, m);
            cbe.State := directoryL1C1_M;
            undefine cbe.requesterL1C1;

            -- [Axiom 1]
            assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
            -- cbe.directoryEventFlag := true;

            return true;
          endif;
          if (inmsg.src = cbe.ownerL1C1) then
            msg := HostRspL1C1(adr,GO_WritePullL1C1,m,inmsg.src);
            Send_H2D_response(msg, m);
            Clear_perm(adr, m);
            cbe.State := directoryL1C1_M_DEvict;

            -- [Axiom 1]
            assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
            cbe.directoryEventFlag := true;

            return true;
          endif;
        
        case RdOwnL1C1:
          -- [Axiom 1]
          assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
          cbe.directoryEventFlag := true;

          msg := HostReqL1C1(adr,SnpInvML1C1,inmsg.src,cbe.ownerL1C1);
          Send_H2D_request(msg, m);
          cbe.ownerL1C1 := inmsg.src;
          Clear_perm(adr, m);
          cbe.State := directoryL1C1_M_RdOwn;
          return true;
        
        case RdSharedL1C1:
          -- [Axiom 1]
          assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
          cbe.directoryEventFlag := true;

          msg := HostReqL1C1(adr,SnpDataL1C1,inmsg.src,cbe.ownerL1C1);
          Send_H2D_request(msg, m);
          AddElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1);
          AddElement_cacheL1C1(cbe.cacheL1C1, inmsg.src);
          cbe.requesterL1C1 := inmsg.src;
          Clear_perm(adr, m);
          cbe.State := directoryL1C1_M_RdShared;
          return true;
        
        else return false;
      endswitch;
      
      case directoryL1C1_M_DEvict:
      switch inmsg.mtype
        case DevDataMsgL1C1:
          cbe.cl := inmsg.cl;
          Clear_perm(adr, m);
          cbe.State := directoryL1C1_I;
          undefine cbe.requesterL1C1;

          -- [Axiom 1]
          assert !isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory ending an event. Why is the directoryEventFlag not set?\n";
          undefine cbe.directoryEventFlag;

          return true;
        
        else return false;
      endswitch;
      
      case directoryL1C1_M_RdOwn:
      switch inmsg.mtype
        case RspIFwdML1C1:
          Clear_perm(adr, m);
          cbe.State := directoryL1C1_M_RdOwn_RspIFwdM;
          return true;
        
        else return false;
      endswitch;
      
      case directoryL1C1_M_RdOwn_RspIFwdM:
      switch inmsg.mtype
        case DevDataMsgL1C1:
          if (cbe.ownerL1C1 != directoryL1C1) then
            msg1 := HostRspL1C1(adr,GO_ML1C1,m,cbe.ownerL1C1);
            Send_H2D_response(msg1, m);
            msg2 := DataFullL1C1(adr,HostDataMsgL1C1,m,cbe.ownerL1C1,inmsg.cl);
            Send_H2D_data(msg2, m);
            cbe.cl := inmsg.cl;
            Clear_perm(adr, m);
            cbe.State := directoryL1C1_M;
            undefine cbe.requesterL1C1;
          else
            cbe.State := directoryL1C1_I;
            undefine cbe.requesterL1C1;
          endif;

          -- [Axiom 1]
          assert !isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory ending an event. Why is the directoryEventFlag not set?\n";
          undefine cbe.directoryEventFlag;

          return true;
        
        else return false;
      endswitch;
      
      case directoryL1C1_M_RdShared:
      switch inmsg.mtype
        case RspSFwdML1C1:
          Clear_perm(adr, m);
          cbe.State := directoryL1C1_M_RdShared_RspSFwdM;
          return true;
        
        else return false;
      endswitch;
      
      case directoryL1C1_M_RdShared_RspSFwdM:
      switch inmsg.mtype
        case DevDataMsgL1C1:
          if (cbe.requesterL1C1 != directoryL1C1) then
            msg1 := HostRspL1C1(adr,GO_SL1C1,m,cbe.requesterL1C1);
            Send_H2D_response(msg1, m);
            msg2 := DataFullL1C1(adr,HostDataMsgL1C1,m,cbe.requesterL1C1,inmsg.cl);
            Send_H2D_data(msg2, m);
          --else
          endif;
          cbe.cl := inmsg.cl;
          Clear_perm(adr, m);
          cbe.State := directoryL1C1_S;

          undefine cbe.requesterL1C1;
          -- cbe.State := directoryL1C1_I;

          -- [Axiom 1]
          assert !isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory ending an event. Why is the directoryEventFlag not set?\n";
          undefine cbe.directoryEventFlag;

          return true;
        
        else return false;
      endswitch;
      
      case directoryL1C1_S:
      switch inmsg.mtype
        case CleanEvictNoDataL1C1:
          -- [Axiom 1]
          assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
          -- cbe.directoryEventFlag := true;

          msg := HostRspL1C1(adr,GO_IL1C1,m,inmsg.src);
          Send_H2D_response(msg, m);
          if (IsElement_cacheL1C1(cbe.cacheL1C1, inmsg.src)) then
            if (VectorCount_cacheL1C1(cbe.cacheL1C1) = 1) then
              RemoveElement_cacheL1C1(cbe.cacheL1C1, inmsg.src);
              Clear_perm(adr, m);
              cbe.State := directoryL1C1_I;
              return true;
            endif;
            if !(VectorCount_cacheL1C1(cbe.cacheL1C1) = 1) then
              RemoveElement_cacheL1C1(cbe.cacheL1C1, inmsg.src);
              Clear_perm(adr, m);
              cbe.State := directoryL1C1_S;
              undefine cbe.requesterL1C1;
              return true;
            endif;
          endif;
          if !(IsElement_cacheL1C1(cbe.cacheL1C1, inmsg.src)) then
            RemoveElement_cacheL1C1(cbe.cacheL1C1, inmsg.src);
            Clear_perm(adr, m);
            cbe.State := directoryL1C1_S;
            return true;
            undefine cbe.requesterL1C1;
          endif;
        
        case DirtyEvictL1C1:
          -- [Axiom 1]
          assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
          -- cbe.directoryEventFlag := true;

          msg := HostRspL1C1(adr,GO_IL1C1,m,inmsg.src);
          Send_H2D_response(msg, m);
          if (IsElement_cacheL1C1(cbe.cacheL1C1, inmsg.src)) then
            if !(VectorCount_cacheL1C1(cbe.cacheL1C1) = 1) then
              RemoveElement_cacheL1C1(cbe.cacheL1C1, inmsg.src);
              Clear_perm(adr, m);
              cbe.State := directoryL1C1_S;
              undefine cbe.requesterL1C1;
              return true;
            endif;
            if (VectorCount_cacheL1C1(cbe.cacheL1C1) = 1) then
              RemoveElement_cacheL1C1(cbe.cacheL1C1, inmsg.src);
              Clear_perm(adr, m);
              cbe.State := directoryL1C1_I;
              undefine cbe.requesterL1C1;
              return true;
            endif;
          endif;
          if !(IsElement_cacheL1C1(cbe.cacheL1C1, inmsg.src)) then
            RemoveElement_cacheL1C1(cbe.cacheL1C1, inmsg.src);
            Clear_perm(adr, m);
            cbe.State := directoryL1C1_S;
            undefine cbe.requesterL1C1;
            return true;
          endif;
        
        case RdOwnL1C1:
          cbe.ownerL1C1 := inmsg.src;
          cbe.acksExpectedL1C1 := VectorCount_cacheL1C1(cbe.cacheL1C1);
          if !(IsElement_cacheL1C1(cbe.cacheL1C1, inmsg.src)) then
            if (IsElement_cacheL1C1(cbe.cacheL1C1, inmsg.dst)) then
              cbe.acksExpectedL1C1 := cbe.acksExpectedL1C1-1;
              cbe.acksReceivedL1C1 := 0;
              if !(cbe.acksExpectedL1C1 != 0) then
                msg := HostRspL1C1(adr,GO_ML1C1,m,cbe.ownerL1C1);
                Send_H2D_response(msg, m);
                msg1 := DataFullL1C1(adr,HostDataMsgL1C1,m,inmsg.src,cbe.cl);
                Send_H2D_data(msg1, m);
                if !(IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
                  Clear_perm(adr, m);
                  cbe.State := directoryL1C1_M;
                  undefine cbe.requesterL1C1;

                  -- [Axiom 1]
                  assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
                  -- cbe.directoryEventFlag := true;

                  return true;
                endif;
                if (IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
                  ClearVector_cacheL1C1(cbe.cacheL1C1);
                  Clear_perm(adr, m);
                  cbe.State := directoryL1C1_M;
                  undefine cbe.requesterL1C1;

                  -- [Axiom 1]
                  assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
                  -- cbe.directoryEventFlag := true;

                  return true;
                endif;
              endif;
              if (cbe.acksExpectedL1C1 != 0) then
                if !(IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
                  msg := HostReqL1C1(adr,SnpInvSL1C1,m,m);
                  Multicast_H2D_request_v_cacheL1C1(msg, cbe.cacheL1C1, m);
                  ClearVector_cacheL1C1(cbe.cacheL1C1);
                  Clear_perm(adr, m);
                  cbe.State := directoryL1C1_SM_Acks;

                  -- [Axiom 1]
                  assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
                  cbe.directoryEventFlag := true;

                  return true;
                endif;
                if (IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
                  RemoveElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1);
                  msg := HostReqL1C1(adr,SnpInvSL1C1,m,m);
                  Multicast_H2D_request_v_cacheL1C1(msg, cbe.cacheL1C1, m);
                  ClearVector_cacheL1C1(cbe.cacheL1C1);
                  AddElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1);
                  Clear_perm(adr, m);
                  cbe.State := directoryL1C1_SM_Acks;

                  -- [Axiom 1]
                  assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
                  cbe.directoryEventFlag := true;

                  return true;
                endif;
              endif;
            endif;
            if !(IsElement_cacheL1C1(cbe.cacheL1C1, inmsg.dst)) then
              cbe.acksReceivedL1C1 := 0;
              if (cbe.acksExpectedL1C1 != 0) then
                if (IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
                  RemoveElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1);
                  msg := HostReqL1C1(adr,SnpInvSL1C1,m,m);
                  Multicast_H2D_request_v_cacheL1C1(msg, cbe.cacheL1C1, m);
                  ClearVector_cacheL1C1(cbe.cacheL1C1);
                  AddElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1);
                  Clear_perm(adr, m);
                  cbe.State := directoryL1C1_SM_Acks;

                  -- [Axiom 1]
                  assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
                  cbe.directoryEventFlag := true;

                  return true;
                endif;
                if !(IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
                  msg := HostReqL1C1(adr,SnpInvSL1C1,m,m);
                  Multicast_H2D_request_v_cacheL1C1(msg, cbe.cacheL1C1, m);
                  ClearVector_cacheL1C1(cbe.cacheL1C1);
                  Clear_perm(adr, m);
                  cbe.State := directoryL1C1_SM_Acks;

                  -- [Axiom 1]
                  assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
                  cbe.directoryEventFlag := true;

                  return true;
                endif;
              endif;
              if !(cbe.acksExpectedL1C1 != 0) then
                msg := HostRspL1C1(adr,GO_ML1C1,m,cbe.ownerL1C1);
                Send_H2D_response(msg, m);
                msg1 := DataFullL1C1(adr,HostDataMsgL1C1,m,inmsg.src,cbe.cl);
                Send_H2D_data(msg1, m);
                if (IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
                  ClearVector_cacheL1C1(cbe.cacheL1C1);
                  Clear_perm(adr, m);
                  cbe.State := directoryL1C1_M;
                  undefine cbe.requesterL1C1;

                  -- [Axiom 1]
                  assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
                  -- cbe.directoryEventFlag := true;

                  return true;
                endif;
                if !(IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
                  Clear_perm(adr, m);
                  cbe.State := directoryL1C1_M;
                  undefine cbe.requesterL1C1;

                  -- [Axiom 1]
                  assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
                  -- cbe.directoryEventFlag := true;

                  return true;
                endif;
              endif;
            endif;
          endif;
          if (IsElement_cacheL1C1(cbe.cacheL1C1, inmsg.src)) then
            cbe.acksExpectedL1C1 := cbe.acksExpectedL1C1-1;
            if (IsElement_cacheL1C1(cbe.cacheL1C1, inmsg.dst)) then
              cbe.acksExpectedL1C1 := cbe.acksExpectedL1C1-1;
              cbe.acksReceivedL1C1 := 0;
              if !(cbe.acksExpectedL1C1 != 0) then
                msg := HostRspL1C1(adr,GO_ML1C1,m,cbe.ownerL1C1);
                Send_H2D_response(msg, m);
                msg1 := DataFullL1C1(adr,HostDataMsgL1C1,m,inmsg.src,cbe.cl);
                Send_H2D_data(msg1, m);
                if !(IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
                  Clear_perm(adr, m);
                  cbe.State := directoryL1C1_M;
                  undefine cbe.requesterL1C1;

                  -- [Axiom 1]
                  assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
                  -- cbe.directoryEventFlag := true;

                  return true;
                endif;
                if (IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
                  ClearVector_cacheL1C1(cbe.cacheL1C1);
                  Clear_perm(adr, m);
                  cbe.State := directoryL1C1_M;
                  undefine cbe.requesterL1C1;

                  -- [Axiom 1]
                  assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
                  -- cbe.directoryEventFlag := true;

                  return true;
                endif;
              endif;
              if (cbe.acksExpectedL1C1 != 0) then
                if (IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
                  RemoveElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1);
                  msg := HostReqL1C1(adr,SnpInvSL1C1,m,m);
                  Multicast_H2D_request_v_cacheL1C1(msg, cbe.cacheL1C1, m);
                  ClearVector_cacheL1C1(cbe.cacheL1C1);
                  AddElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1);
                  Clear_perm(adr, m);
                  cbe.State := directoryL1C1_SM_Acks;

                  -- [Axiom 1]
                  assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
                  cbe.directoryEventFlag := true;

                  return true;
                endif;
                if !(IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
                  msg := HostReqL1C1(adr,SnpInvSL1C1,m,m);
                  Multicast_H2D_request_v_cacheL1C1(msg, cbe.cacheL1C1, m);
                  ClearVector_cacheL1C1(cbe.cacheL1C1);
                  Clear_perm(adr, m);
                  cbe.State := directoryL1C1_SM_Acks;

                  -- [Axiom 1]
                  assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
                  cbe.directoryEventFlag := true;

                  return true;
                endif;
              endif;
            endif;
            if !(IsElement_cacheL1C1(cbe.cacheL1C1, inmsg.dst)) then
              cbe.acksReceivedL1C1 := 0;
              if (cbe.acksExpectedL1C1 != 0) then
                if !(IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
                  msg := HostReqL1C1(adr,SnpInvSL1C1,m,m);
                  Multicast_H2D_request_v_cacheL1C1(msg, cbe.cacheL1C1, m);
                  ClearVector_cacheL1C1(cbe.cacheL1C1);
                  Clear_perm(adr, m);
                  cbe.State := directoryL1C1_SM_Acks;

                  -- [Axiom 1]
                  assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
                  cbe.directoryEventFlag := true;

                  return true;
                endif;
                if (IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
                  RemoveElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1);
                  msg := HostReqL1C1(adr,SnpInvSL1C1,m,m);
                  Multicast_H2D_request_v_cacheL1C1(msg, cbe.cacheL1C1, m);
                  ClearVector_cacheL1C1(cbe.cacheL1C1);
                  AddElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1);
                  Clear_perm(adr, m);
                  cbe.State := directoryL1C1_SM_Acks;

                  -- [Axiom 1]
                  assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
                  cbe.directoryEventFlag := true;

                  return true;
                endif;
              endif;
              if !(cbe.acksExpectedL1C1 != 0) then
                msg := HostRspL1C1(adr,GO_ML1C1,m,cbe.ownerL1C1);
                Send_H2D_response(msg, m);
                msg1 := DataFullL1C1(adr,HostDataMsgL1C1,m,inmsg.src,cbe.cl);
                Send_H2D_data(msg1, m);
                if !(IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
                  Clear_perm(adr, m);
                  cbe.State := directoryL1C1_M;
                  undefine cbe.requesterL1C1;

                  -- [Axiom 1]
                  assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
                  -- cbe.directoryEventFlag := true;

                  return true;
                endif;
                if (IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
                  ClearVector_cacheL1C1(cbe.cacheL1C1);
                  Clear_perm(adr, m);
                  cbe.State := directoryL1C1_M;
                  undefine cbe.requesterL1C1;

                  -- [Axiom 1]
                  assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
                  -- cbe.directoryEventFlag := true;

                  return true;
                endif;
              endif;
            endif;
          endif;
        
        case RdSharedL1C1:
          -- [Axiom 1]
          assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
          -- cbe.directoryEventFlag := true;

          msg := HostRspL1C1(adr,GO_SL1C1,m,inmsg.src);
          Send_H2D_response(msg, m);
          msg1 := DataFullL1C1(adr,HostDataMsgL1C1,m,inmsg.src,cbe.cl);
          Send_H2D_data(msg1, m);
          AddElement_cacheL1C1(cbe.cacheL1C1, inmsg.src);
          Clear_perm(adr, m);
          cbe.State := directoryL1C1_S;
          undefine cbe.requesterL1C1;
          return true;
        
        else return false;
      endswitch;
      
      case directoryL1C1_SM_Acks:
      switch inmsg.mtype
        case RspIHitSEL1C1:
          cbe.acksReceivedL1C1 := cbe.acksReceivedL1C1+1;
          if !(cbe.acksReceivedL1C1 = cbe.acksExpectedL1C1) then
            Clear_perm(adr, m);
            cbe.State := directoryL1C1_SM_Acks;
            return true;
          endif;
          if (cbe.acksReceivedL1C1 = cbe.acksExpectedL1C1) then
            undefine cbe.acksReceivedL1C1;
            -- Proxy Inval Guard
            if (cbe.ownerL1C1 = directoryL1C1) then
              cbe.State := directoryL1C1_I;

              -- [Axiom 1]
              assert !isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory ending an event. Why is the directoryEventFlag not set?\n";
              undefine cbe.directoryEventFlag;

              undefine cbe.requesterL1C1;
              return true;
            else
              msg1 := HostRspL1C1(adr,GO_ML1C1,m,cbe.ownerL1C1);
              Send_H2D_response(msg1, m);
              msg2 := DataFullL1C1(adr,HostDataMsgL1C1,m,cbe.ownerL1C1,cbe.cl);
              Send_H2D_data(msg2, m);
              if !(IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
                Clear_perm(adr, m);
                cbe.State := directoryL1C1_M;
                undefine cbe.requesterL1C1;

                -- [Axiom 1]
                assert !isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory ending an event. Why is the directoryEventFlag not set?\n";
                undefine cbe.directoryEventFlag;

                return true;
              endif;
              if (IsElement_cacheL1C1(cbe.cacheL1C1, cbe.ownerL1C1)) then
                ClearVector_cacheL1C1(cbe.cacheL1C1);
                Clear_perm(adr, m);
                cbe.State := directoryL1C1_M;
                undefine cbe.requesterL1C1;

                -- [Axiom 1]
                assert !isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory ending an event. Why is the directoryEventFlag not set?\n";
                undefine cbe.directoryEventFlag;

                return true;
              endif;
            endif;
          endif;
        
        else return false;
      endswitch;
      
      case directoryL1C1_dE_RdShared_x_pI_load:
      switch inmsg.mtype
        case RspSFwdML1C1:                                                      
          cbe.State := directoryL1C1_E_RspSFwdM;                                
          return true;
        case RspSHitSEL1C1:
          msg1_GO_SL1 := HostRspL1C1(adr,GO_SL1C1,m,inmsg.src);
          msg2_HostDataMsgL1 := DataFullL1C1(adr,HostDataMsgL1C1,m,inmsg.src,cbe.cl);
          cbe.cl := msg2_HostDataMsgL1.cl;
          msg_CleanEvictNoDataL1 := DevReqL1C1(adr,CleanEvictNoDataL1C1,m,m);
          msg_GO_IL1 := HostRspL1C1(adr,GO_IL1C1,m,msg_CleanEvictNoDataL1.src);
          if (IsElement_cacheL1C1(cbe.cacheL1C1, msg_CleanEvictNoDataL1.src)) then
            if !(VectorCount_cacheL1C1(cbe.cacheL1C1) = 1) then
              RemoveElement_cacheL1C1(cbe.cacheL1C1, msg_CleanEvictNoDataL1.src);
              Clear_perm(adr, m);
              cbe.State := directoryL1C1_S;
              return true;
            endif;
            if (VectorCount_cacheL1C1(cbe.cacheL1C1) = 1) then
              RemoveElement_cacheL1C1(cbe.cacheL1C1, msg_CleanEvictNoDataL1.src);
              Clear_perm(adr, m);
              cbe.State := directoryL1C1_I;
              return true;
            endif;
          endif;
          if !(IsElement_cacheL1C1(cbe.cacheL1C1, msg_CleanEvictNoDataL1.src)) then
            RemoveElement_cacheL1C1(cbe.cacheL1C1, msg_CleanEvictNoDataL1.src);
            Clear_perm(adr, m);
            cbe.State := directoryL1C1_S;
            return true;
          endif;
        
        else return false;
      endswitch;
      
    endswitch;
    endalias;
    endalias;
    return false;
    end;
    
    function FSM_MSG_cacheL1C1(inmsg:Message; m:OBJSET_cacheL1C1) : boolean;
    var msg: Message;
    var msg1: Message;
    var msg2: Message;
    var msg3: Message;
    begin
      alias adr: inmsg.adr do
      alias cbe: i_cacheL1C1[m].cb[adr] do
    switch cbe.State
      case cacheL1C1_E:
      switch inmsg.mtype
        case SnpDataL1C1:
          msg := DevRspL1C1(adr,RspSHitSEL1C1,inmsg.src,directoryL1C1);
          Send_D2H_response(msg, m);
          Clear_perm(adr, m); Set_perm(load, adr, m);
          cbe.State := cacheL1C1_S;
          return true;
        
        case SnpInvML1C1:
          msg := DevRspL1C1(adr,RspIHitSEL1C1,inmsg.src,directoryL1C1);
          Send_D2H_response(msg, m);
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_I;
          return true;
        
        else return false;
      endswitch;
      
      case cacheL1C1_E_evict:
      switch inmsg.mtype
        case GO_IL1C1:
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_I;
          return true;
        
        case SnpDataL1C1:
          msg1 := DevRspL1C1(adr,RspSHitSEL1C1,inmsg.src,directoryL1C1);
          Send_D2H_response(msg1, m);
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_E_evict_SnpData;
          return true;
        
        case SnpInvML1C1:
          msg1 := DevRspL1C1(adr,RspIHitSEL1C1,inmsg.src,directoryL1C1);
          Send_D2H_response(msg1, m);
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_E_evict_SnpInvM;
          return true;
        
        else return false;
      endswitch;
      
      case cacheL1C1_E_evict_SnpData:
      switch inmsg.mtype
        case GO_IL1C1:
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_I;
          return true;
        
        case SnpInvSL1C1:
          msg1 := DevRspL1C1(adr,RspIHitSEL1C1,inmsg.src,directoryL1C1);
          Send_D2H_response(msg1, m);
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_E_evict_SnpData_SnpInvS;
          return true;
        
        else return false;
      endswitch;
      
      case cacheL1C1_E_evict_SnpData_SnpInvS:
      switch inmsg.mtype
        case GO_IL1C1:
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_I;
          return true;
        
        else return false;
      endswitch;
      
      case cacheL1C1_E_evict_SnpInvM:
      switch inmsg.mtype
        case GO_IL1C1:
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_I;
          return true;
        
        else return false;
      endswitch;
      
      case cacheL1C1_I:
      switch inmsg.mtype
        else return false;
      endswitch;
      
      case cacheL1C1_I_load:
      switch inmsg.mtype
        case GO_SL1C1:
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_I_load_GO_S;
          return true;
        
        else return false;
      endswitch;
      
      case cacheL1C1_I_load_GO_S:
      switch inmsg.mtype
        case HostDataMsgL1C1:
          cbe.cl := inmsg.cl;
          Clear_perm(adr, m); Set_perm(load, adr, m);
          cbe.State := cacheL1C1_S;
          return true;
        
        else return false;
      endswitch;
      
      case cacheL1C1_I_store:
      switch inmsg.mtype
        case GO_EL1C1:
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_I_store_GO_E;
          return true;
        
        case GO_ML1C1:
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_I_store_GO_M;
          return true;
        
        else return false;
      endswitch;
      
      case cacheL1C1_I_store_GO_E:
      switch inmsg.mtype
        case HostDataMsgL1C1:
          cbe.cl := inmsg.cl;
          Clear_perm(adr, m); Set_perm(store, adr, m); Set_perm(load, adr, m);
          cbe.State := cacheL1C1_E;
          return true;
        
        else return false;
      endswitch;
      
      case cacheL1C1_I_store_GO_M:
      switch inmsg.mtype
        case HostDataMsgL1C1:
          cbe.cl := inmsg.cl;
          Clear_perm(adr, m); Set_perm(load, adr, m); Set_perm(store, adr, m);
          cbe.State := cacheL1C1_M;
          return true;
        
        else return false;
      endswitch;
      
      case cacheL1C1_M:
      switch inmsg.mtype
        case SnpDataL1C1:
          msg := DevRspL1C1(adr,RspSFwdML1C1,inmsg.src,directoryL1C1);
          Send_D2H_response(msg, m);
          msg1 := DataFullL1C1(adr,DevDataMsgL1C1,inmsg.src,directoryL1C1,cbe.cl);
          Send_D2H_data(msg1, m);
          Clear_perm(adr, m); Set_perm(load, adr, m);
          cbe.State := cacheL1C1_S;
          return true;
        
        case SnpInvML1C1:
          msg := DevRspL1C1(adr,RspIFwdML1C1,inmsg.src,directoryL1C1);
          Send_D2H_response(msg, m);
          msg1 := DataFullL1C1(adr,DevDataMsgL1C1,inmsg.src,directoryL1C1,cbe.cl);
          Send_D2H_data(msg1, m);
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_I;
          return true;
        
        else return false;
      endswitch;
      
      case cacheL1C1_M_evict:
      switch inmsg.mtype
        case GO_WritePullL1C1:
          msg1 := DataFullL1C1(adr,DevDataMsgL1C1,m,directoryL1C1,cbe.cl);
          Send_D2H_data(msg1, m);
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_I;
          return true;
        
        case SnpDataL1C1:
          msg1 := DevRspL1C1(adr,RspSFwdML1C1,inmsg.src,directoryL1C1);
          Send_D2H_response(msg1, m);
          msg2 := DataFullL1C1(adr,DevDataMsgL1C1,inmsg.src,directoryL1C1,cbe.cl);
          Send_D2H_data(msg2, m);
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_M_evict_SnpData;
          return true;
        
        case SnpInvML1C1:
          msg1 := DevRspL1C1(adr,RspIFwdML1C1,inmsg.src,directoryL1C1);
          Send_D2H_response(msg1, m);
          msg2 := DataFullL1C1(adr,DevDataMsgL1C1,inmsg.src,directoryL1C1,cbe.cl);
          Send_D2H_data(msg2, m);
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_M_evict_SnpInvM;
          return true;
        
        else return false;
      endswitch;
      
      case cacheL1C1_M_evict_SnpData:
      switch inmsg.mtype
        case GO_IL1C1:
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_I;
          return true;
        
        case SnpInvSL1C1:
          msg3 := DevRspL1C1(adr,RspIHitSEL1C1,inmsg.src,directoryL1C1);
          Send_D2H_response(msg3, m);
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_M_evict_SnpData_SnpInvS;
          return true;
        
        else return false;
      endswitch;
      
      case cacheL1C1_M_evict_SnpData_SnpInvS:
      switch inmsg.mtype
        case GO_IL1C1:
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_I;
          return true;
        
        else return false;
      endswitch;
      
      case cacheL1C1_M_evict_SnpInvM:
      switch inmsg.mtype
        case GO_IL1C1:
          Clear_perm(adr, m);
          -- Go to I
          cbe.State := cacheL1C1_I;
          return true;
        
        else return false;
      endswitch;
      
      case cacheL1C1_S:
      switch inmsg.mtype
        case SnpInvSL1C1:
          msg := DevRspL1C1(adr,RspIHitSEL1C1,m,directoryL1C1);
          Send_D2H_response(msg, m);
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_I;
          return true;
        
        else return false;
      endswitch;
      
      case cacheL1C1_S_evict:
      switch inmsg.mtype
        case GO_IL1C1:
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_I;
          return true;
        
        case SnpInvSL1C1:
          msg1 := DevRspL1C1(adr,RspIHitSEL1C1,m,directoryL1C1);
          Send_D2H_response(msg1, m);
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_S_evict_SnpInvS;
          return true;
        
        else return false;
      endswitch;
      
      case cacheL1C1_S_evict_SnpInvS:
      switch inmsg.mtype
        case GO_IL1C1:
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_I;
          return true;
        
        else return false;
      endswitch;
      
      case cacheL1C1_S_store:
      switch inmsg.mtype
        case GO_ML1C1:
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_S_store_GO_M;
          return true;
        
        case SnpInvSL1C1:
          msg := DevRspL1C1(adr,RspIHitSEL1C1,m,directoryL1C1);
          Send_D2H_response(msg, m);
          Clear_perm(adr, m);
          cbe.State := cacheL1C1_I_store;
          return true;
        
        else return false;
      endswitch;
      
      case cacheL1C1_S_store_GO_M:
      switch inmsg.mtype
        case HostDataMsgL1C1:
          cbe.cl := inmsg.cl;
          Clear_perm(adr, m); Set_perm(load, adr, m); Set_perm(store, adr, m);
          cbe.State := cacheL1C1_M;
          return true;
        
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
  end;
  

--Backend/Murphi/MurphiModular/GenRules
  ----Backend/Murphi/MurphiModular/Rules/GenAccessRuleSet
    ruleset m:OBJSET_directoryL1C1 do
    ruleset adr:Address do
      alias cbe:i_directoryL1C1[m].cb[adr] do
    
      rule "directoryL1C1_E_load"
        cbe.State = directoryL1C1_E & network_ready() 
      ==>
        -- [Axiom 1]
        assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
        cbe.directoryEventFlag := true;

        FSM_Access_directoryL1C1_E_load(adr, m);
        
      endrule;

      rule "directoryL1C1_E_store"
        cbe.State = directoryL1C1_E & network_ready() 
      ==>
        -- [Axiom 1]
        assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
        cbe.directoryEventFlag := true;

        FSM_Access_directoryL1C1_E_store(adr, m);
        
      endrule;
    
      -- [TODOs]

      rule "directoryL1C1_M_load"
        cbe.State = directoryL1C1_M & network_ready() 
      ==>
        -- [Axiom 1]
        assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
        cbe.directoryEventFlag := true;

        FSM_Access_directoryL1C1_M_load(adr, m);
        
      endrule;

      rule "directoryL1C1_M_store"
        cbe.State = directoryL1C1_M & network_ready() 
      ==>
        -- [Axiom 1]
        assert isundefined(cbe.directoryEventFlag) ">[Axiom 1] Directory starting an event. Why is the directory Event Flag set?\n";
        cbe.directoryEventFlag := true;

        FSM_Access_directoryL1C1_M_store(adr, m);
        
      endrule;
    
      rule "directoryL1C1_S_store"
        cbe.State = directoryL1C1_S & network_ready() 
      ==>
        -- [Axiom 1] asserts in procedure below
        FSM_Access_directoryL1C1_S_store(adr, m);
        
      endrule;
      /*
      rule "directoryL1C1_I_store"
        cbe.State = directoryL1C1_I 
      ==>
        FSM_Access_directoryL1C1_I_store(adr, m);
        
      endrule;
    
      rule "directoryL1C1_I_load"
        cbe.State = directoryL1C1_I 
      ==>
        FSM_Access_directoryL1C1_I_load(adr, m);
        
      endrule;
    
      rule "directoryL1C1_S_load"
        cbe.State = directoryL1C1_S 
      ==>
        FSM_Access_directoryL1C1_S_load(adr, m);
        
      endrule;
      */
    
      endalias;
    endruleset;
    endruleset;
    
    ruleset m:OBJSET_cacheL1C1 do
    ruleset adr:Address do
      alias cbe:i_cacheL1C1[m].cb[adr] do
    
      rule "cacheL1C1_E_evict"
        cbe.State = cacheL1C1_E & network_ready() 
      ==>
        FSM_Access_cacheL1C1_E_evict(adr, m);
        Clear_perm(adr, m);
        
      endrule;
    
      rule "cacheL1C1_E_store"
        cbe.State = cacheL1C1_E 
      ==>
        FSM_Access_cacheL1C1_E_store(adr, m);
        
      endrule;
    
      rule "cacheL1C1_E_load"
        cbe.State = cacheL1C1_E 
      ==>
        FSM_Access_cacheL1C1_E_load(adr, m);
        
      endrule;
    
      rule "cacheL1C1_I_evict"
        cbe.State = cacheL1C1_I 
      ==>
        FSM_Access_cacheL1C1_I_evict(adr, m);
        
      endrule;
    
      rule "cacheL1C1_I_store"
        cbe.State = cacheL1C1_I & network_ready() 
      ==>
        FSM_Access_cacheL1C1_I_store(adr, m);
        
      endrule;
    
      rule "cacheL1C1_I_load"
        cbe.State = cacheL1C1_I & network_ready() 
      ==>
        FSM_Access_cacheL1C1_I_load(adr, m);
        
      endrule;
    
      rule "cacheL1C1_M_evict"
        cbe.State = cacheL1C1_M & network_ready() 
      ==>
        FSM_Access_cacheL1C1_M_evict(adr, m);
        Clear_perm(adr, m);
        
      endrule;
    
      rule "cacheL1C1_M_load"
        cbe.State = cacheL1C1_M 
      ==>
        FSM_Access_cacheL1C1_M_load(adr, m);
        
      endrule;
    
      rule "cacheL1C1_M_store"
        cbe.State = cacheL1C1_M 
      ==>
        FSM_Access_cacheL1C1_M_store(adr, m);
        
      endrule;
    
      rule "cacheL1C1_S_evict"
        cbe.State = cacheL1C1_S & network_ready() 
      ==>
        FSM_Access_cacheL1C1_S_evict(adr, m);
        Clear_perm(adr, m);
        
      endrule;
    
      rule "cacheL1C1_S_store"
        cbe.State = cacheL1C1_S & network_ready() 
      ==>
        FSM_Access_cacheL1C1_S_store(adr, m);
        
      endrule;
    
      rule "cacheL1C1_S_load"
        cbe.State = cacheL1C1_S 
      ==>
        FSM_Access_cacheL1C1_S_load(adr, m);
        
      endrule;
    
    
      endalias;
    endruleset;
    endruleset;
    
  ----Backend/Murphi/MurphiModular/Rules/GenEventRuleSet
  ----Backend/Murphi/MurphiModular/Rules/GenNetworkRule
    ruleset dst:Machines do
        ruleset src: Machines do
            alias msg:H2D_data[dst][0] do
              rule "Receive H2D_data"
                cnt_H2D_data[dst] > 0
              ==>
            if IsMember(dst, OBJSET_directoryL1C1) then
              if FSM_MSG_directoryL1C1(msg, dst) then
                  Pop_H2D_data(dst, src);
              endif;
            elsif IsMember(dst, OBJSET_cacheL1C1) then
              if FSM_MSG_cacheL1C1(msg, dst) then
                  Pop_H2D_data(dst, src);
              endif;
            else error "unknown machine";
            endif;
    
              endrule;
            endalias;
        endruleset;
    endruleset;
    
    ruleset dst:Machines do
        ruleset src: Machines do
            alias msg:D2H_data[dst][0] do
              rule "Receive D2H_data"
                cnt_D2H_data[dst] > 0
              ==>
            if IsMember(dst, OBJSET_directoryL1C1) then
              if FSM_MSG_directoryL1C1(msg, dst) then
                  Pop_D2H_data(dst, src);
              endif;
            elsif IsMember(dst, OBJSET_cacheL1C1) then
              if FSM_MSG_cacheL1C1(msg, dst) then
                  Pop_D2H_data(dst, src);
              endif;
            else error "unknown machine";
            endif;
    
              endrule;
            endalias;
        endruleset;
    endruleset;
    
    ruleset dst:Machines do
        choose midx:D2H_response[dst] do
            alias mach:D2H_response[dst] do
            alias msg:mach[midx] do
              rule "Receive D2H_response"
                !isundefined(msg.mtype)
              ==>
            if IsMember(dst, OBJSET_directoryL1C1) then
              if FSM_MSG_directoryL1C1(msg, dst) then
                MultiSetRemove(midx, mach);
              endif;
            elsif IsMember(dst, OBJSET_cacheL1C1) then
              if FSM_MSG_cacheL1C1(msg, dst) then
                MultiSetRemove(midx, mach);
              endif;
            else error "unknown machine";
            endif;
    
              endrule;
            endalias;
            endalias;
        endchoose;
    endruleset;
    
    ruleset dst:Machines do
        choose midx:H2D_response[dst] do
            alias mach:H2D_response[dst] do
            alias msg:mach[midx] do
              rule "Receive H2D_response"
                !isundefined(msg.mtype)
              ==>
            if IsMember(dst, OBJSET_directoryL1C1) then
              if FSM_MSG_directoryL1C1(msg, dst) then
                MultiSetRemove(midx, mach);
              endif;
            elsif IsMember(dst, OBJSET_cacheL1C1) then
              if FSM_MSG_cacheL1C1(msg, dst) then
                MultiSetRemove(midx, mach);
              endif;
            else error "unknown machine";
            endif;
    
              endrule;
            endalias;
            endalias;
        endchoose;
    endruleset;
    
    ruleset dst:Machines do
        choose midx:H2D_request[dst] do
            alias mach:H2D_request[dst] do
            alias msg:mach[midx] do
              rule "Receive H2D_request"
                !isundefined(msg.mtype)
              ==>
            if IsMember(dst, OBJSET_directoryL1C1) then
              if FSM_MSG_directoryL1C1(msg, dst) then
                MultiSetRemove(midx, mach);
              endif;
            elsif IsMember(dst, OBJSET_cacheL1C1) then
              if FSM_MSG_cacheL1C1(msg, dst) then
                MultiSetRemove(midx, mach);
              endif;
            else error "unknown machine";
            endif;
    
              endrule;
            endalias;
            endalias;
        endchoose;
    endruleset;
    
    ruleset dst:Machines do
        choose midx:D2H_request[dst] do
            alias mach:D2H_request[dst] do
            alias msg:mach[midx] do
              rule "Receive D2H_request"
                !isundefined(msg.mtype)
              ==>
            if IsMember(dst, OBJSET_directoryL1C1) then
              if FSM_MSG_directoryL1C1(msg, dst) then
                MultiSetRemove(midx, mach);
              endif;
            elsif IsMember(dst, OBJSET_cacheL1C1) then
              if FSM_MSG_cacheL1C1(msg, dst) then
                MultiSetRemove(midx, mach);
              endif;
            else error "unknown machine";
            endif;
    
              endrule;
            endalias;
            endalias;
        endchoose;
    endruleset;
    

--Backend/Murphi/MurphiModular/GenStartStates

  startstate
    System_Reset();
  endstartstate;

--Backend/Murphi/MurphiModular/GenInvariant
