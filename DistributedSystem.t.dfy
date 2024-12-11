include "Network.t.dfy"
//#extract Network.t.template inherit Network.t.dfy
include "Host.v.dfy"
//#extract Host.v.template inherit Host.v.dfy

module DistributedSystem {
  import opened UtilitiesLibrary
  import opened Types
  import Network
  import Host

  type HostId = Network.HostId

/*{*/
  datatype Constants = Constants(hosts: seq<Host.Constants>, network: Network.Constants)
  {
    ghost predicate WF() {
      0 < |hosts|
    }

    ghost predicate ValidHostId(id: HostId) {
      id < |hosts|
    }
  }
  datatype Variables = Variables(hosts: seq<Host.Variables>, network: Network.Variables)
  {
    ghost predicate WF(c: Constants) {
      && c.WF()
      && |hosts| == |c.hosts|
    }
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && Host.GroupInit(c.hosts, v.hosts)
    && Network.Init(c.network, v.network)
  }

  ghost predicate HostAction(c: Constants, v: Variables, v': Variables, event: Event, hostid: HostId, msgOps: Network.MessageOps){
    && v.WF(c)
    && v'.WF(c)
    && c.ValidHostId(hostid)
    && Host.Next(c.hosts[hostid], v.hosts[hostid], v'.hosts[hostid], event, msgOps)
    && Network.Next(c.network, v.network, v'.network, msgOps)
  }

  datatype Step =
    | HostActionStep(hostid: HostId, msgOps: Network.MessageOps) 

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, event: Event, step: Step)
    {
        && HostAction(c, v, v', event, step.hostid, step.msgOps)
    }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, event: Event)
    {
        exists step :: NextStep(c, v, v', event, step)
    }
/*}*/
}
