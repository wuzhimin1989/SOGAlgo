using System;
using System.Collections.Generic;
//using System.Reactive.Concurrency;
using System.Linq;
using System.Text;
using System.Collections;
using PAT.Common.Classes.DataStructure;
using System.ComponentModel;
using PAT.CLTS.LTS.Monolithic;
using PAT.Common.Classes.BA;
using PAT.Common.Classes.Expressions;
using PAT.Common.Classes.Expressions.ExpressionClass;
using PAT.Common.Classes.SemanticModels.LTS.BDD;
using PAT.Common.Classes.SemanticModels.LTS.Assertion;
using PAT.Common.Classes.Ultility;
using PAT.Common.Classes.ModuleInterface;
//using Transition = PAT.Common.Classes.SemanticModels.LTS.BDD.Transition;
using Transition = PAT.CLTS.LTS.Monolithic.Transition;
using State = PAT.CLTS.LTS.Monolithic.State;

namespace PAT.CLTS.Assertions
{
    public class OGTransition
    {
        public Transition practical_transition;
        public OGMeta_state FromMstate;
        public OGMeta_state ToMstate;

        public string FromSynMstate;
        public string ToSynMstate;

        public string OGTKey;

        public OGTransition()
        {
            practical_transition = new Transition();
            FromMstate = new OGMeta_state();
            ToMstate = new OGMeta_state();
        }
    }

    /********Class Meta_State****/
    public class OGMeta_state
    {
        public List<State> ReachableStates;
        public List<Transition> UobTransitions;
        public List<Transition> OutgoingTransitions;
        public List<OGTransition> OGOutgoingTransitions;

        public string ID;
        public string MKey; //new

        /****scc****/
        private int Index;
        private Stack<State> S;

        public bool IfCycle;
        public bool IfDead;

        public OGMeta_state()
        {
            Index = 0;
            
            S = new Stack<State>();
            ReachableStates = new List<State>();
            UobTransitions = new List<Transition>();
            OutgoingTransitions = new List<Transition>();
            OGOutgoingTransitions = new List<OGTransition>();
            //MKey = new string('R');
        }

        /*private bool IfStrongConnect(State s)
        {
            s.lowlink = Index;
            s.Index = Index;
            Index = Index + 1;

            S.Push(s);

            foreach (Transition t in s.OutgoingTransitions)
            {
                if (UobTransitions.Contains(t))
                {
                    if (t.ToState.Index == -1)
                    {   
                        IfStrongConnect(t.ToState);
                        if(s.lowlink > t.ToState.lowlink)
                            s.lowlink = t.ToState.lowlink;
                    }
                    else if (S.Contains(t.ToState))
                    {
                        if (s.lowlink > t.ToState.Index)
                        {
                            s.lowlink = t.ToState.Index;
                        }
                     }
                }
            }

            if(s.lowlink==s.Index)
            {
                while(s.ID==(S.Pop()).ID);
                return true;
            }
            else
            {
                return false;
            }
        }*/ //recrusive version change to iterative version

        public int DefineCycle()
        {
            //bool ifscc = false;
            int Count = 0;
            int j = 0;            
            State tmp1;
            State tmp2;
            Transition tmpt;

            if (this.ReachableStates.Count == 1 && this.OutgoingTransitions.Count == 0)
            {
                this.IfCycle = false;
                return 0;
            }
            if (this.ReachableStates.Count > this.UobTransitions.Count)
            {
                this.IfCycle = false;
                return 0;
            }

            Stack<State> tmpstack = new Stack<State>(); //
            Stack<State> explored = new Stack<State>(); //
            
            List<State> todo = new List<State>();
            Dictionary<State, Stack<Transition>> outgoingtransition = new Dictionary<State,Stack<Transition>>();
            Stack<Transition> tmpkv;

            foreach (State m in this.ReachableStates)
            {
                tmpkv =  new Stack<Transition>();
                foreach (Transition t in m.OutgoingTransitions)
                {
                    tmpkv.Push(t);
                }
                m.InitIndex();
                outgoingtransition.Add(m,tmpkv);             
            }
            foreach (KeyValuePair<State,Stack<Transition>> k in outgoingtransition)
            {
                State s = k.Key;
                if (s.Index == -1)
                {
                    s.lowlink = Index;
                    s.Index = Index;
                    explored.Push(s);
                    tmpstack.Push(s);

                    Index++;

                    while (explored.Count != 0)
                    {
                        tmp1 = explored.Peek();
                        tmpkv = outgoingtransition[tmp1];
                        if (tmpkv.Count > 0)
                        {
                            tmpt = tmpkv.Pop();
                            tmp2 = tmpt.ToState;
                            if (UobTransitions.Contains(tmpt))
                            {
                                if (tmp2.Index == -1)
                                {
                                    tmp2.lowlink = Index;
                                    tmp2.Index = Index;
                                    //explored.Push(tmp2);
                                    tmpstack.Push(tmp2);
                                    Index++;
                                }
                                else if (tmp2.Index < tmp1.Index && tmpstack.Contains(tmp2))
                                {
                                    if (tmp1.lowlink > tmp2.Index)
                                    {
                                        tmp1.lowlink = tmp2.Index;
                                    }
                                }
                            }
                        }
                        else
                        {
                            explored.Pop();
                            if(tmp1.lowlink==tmp1.Index)
                            {
                                Count++;
                                while(tmpstack.Count != 0 && tmpstack.Peek().Index > tmp1.Index)
                                    tmpstack.Pop();
                            }
                            if(explored.Count != 0)
                            {
                                if((explored.Peek()).lowlink > tmp1.lowlink)
                                    (explored.Peek()).lowlink = tmp1.lowlink;
                            }
                                

                        }
                    }
                }
            }
            if (Count == 0)
            {
                this.IfCycle = false;
            }
            else
                this.IfCycle = true;
            
            return Count;
        }

        public int DefineDead()
        {
            bool ifdead;
            int count = 0;
            foreach (State s in ReachableStates)
            {
                ifdead = true;
                foreach (Transition t in s.OutgoingTransitions) 
                {
                    if (!string.Equals(t.ToState.ID, s.ID))
                    {
                        ifdead = false;
                        break;
                    }
                }               
                if(ifdead == false)
                    count++;
            }
            if (count == ReachableStates.Count)
                this.IfDead = false;
            else
                this.IfDead = true;

            return (ReachableStates.Count - count);
        }

        
        public List<KeyValuePair<OGMeta_state, string>> MakeOneFullMove()
        {
            List<KeyValuePair<OGMeta_state, string>> returnlist = new List<KeyValuePair<OGMeta_state, string>>();
            foreach (OGTransition ogt in this.OGOutgoingTransitions)
            {
                returnlist.Add(new KeyValuePair<OGMeta_state,string>(ogt.ToMstate,ogt.practical_transition.Event.ToString()));
            }
            return returnlist;
        }

       
        
        public List<OGMeta_state> MakeOneMove(string evt)
        //public List<KeyValuePair<OGMeta_state, string>> MakeOneMove(string evt)
        {
            //List<KeyValuePair<OGMeta_state,string>> returnlist = new List<KeyValuePair<OGMeta_state,string>>();
            List<OGMeta_state> returnlist = new List<OGMeta_state>();
            List<KeyValuePair<OGMeta_state, string>> steps = MakeOneFullMove();
            foreach (KeyValuePair<OGMeta_state, string> st in steps)
            {
                if (st.Value == evt)
                {
                    returnlist.Add(st.Key);
                }
            }


            return returnlist;
        }
    }


    /***********************************class Observation Graph******************/
    public class ModularOG
    {
        public Automaton graph;  //configbase?
        public OGMeta_state InitialMetaState;
        public List<OGMeta_state> MetaStates;
        //public List<Transition> ObTranstions;  //must be events
        public List<string> OBs;
        public List<OGTransition> OGTranstions;
 
        public Stack<State> StatesStack;

        public string ID;

        public ModularOG(Automaton LTSgraph)
        {
            graph = LTSgraph;
            InitialMetaState = new OGMeta_state();
            MetaStates = new List<OGMeta_state>();
            //ObTranstions = new List<Transition>();
            OBs = new List<string>();
            StatesStack = new Stack<State>();
            OGTranstions = new List<OGTransition>();
        }
        public bool GenerateReachableState(ref OGMeta_state NewMetastate, State Ori)
        {
            int StateClosureCount = 0;
            State tmpstate = new State();
            State tmpstate2 = new State();
            List<string> tmplist = new List<string>();

            NewMetastate.ReachableStates.Add(Ori);
            tmplist.Add(Ori.ID);
            Ori.BelongMID.Add(NewMetastate.ID);

            if (Ori.OutgoingTransitions.Count() >= 0)
            {
                foreach (Transition t in Ori.OutgoingTransitions)
                {

                    if (OBs.Contains(t.Event.ToString()))   //use event to define obs
                    {
                        NewMetastate.OutgoingTransitions.Add(t);
                    }
                    else
                    {

                        NewMetastate.UobTransitions.Add(t);

                        if (!NewMetastate.ReachableStates.Contains(t.ToState))
                        {
                            t.ToState.BelongMID.Add(NewMetastate.ID);
                            NewMetastate.ReachableStates.Add(t.ToState);
                            tmplist.Add(t.ToState.ID); ;

                            StatesStack.Push(t.ToState);
                            StateClosureCount++;
                            while (StatesStack.Count > 0)
                            {
                                tmpstate2 = StatesStack.Pop();
                                foreach (Transition t2 in tmpstate2.OutgoingTransitions) //use event to replace
                                {
                                    if (OBs.Contains(t2.Event.ToString()))   //use event to define
                                    {
                                        NewMetastate.OutgoingTransitions.Add(t2);
                                    }
                                    else
                                    {
                                        NewMetastate.UobTransitions.Add(t2);

                                        if (!NewMetastate.ReachableStates.Contains(t2.ToState))
                                        {
                                            t2.ToState.BelongMID.Add(NewMetastate.ID);
                                            NewMetastate.ReachableStates.Add(t2.ToState);
                                            tmplist.Add(t2.ToState.ID); ;

                                            StatesStack.Push(t2.ToState);
                                            StateClosureCount++;
                                        }
                                    }
                                }
                            }
                        }

                    }
                }

            }
            else
            {
                return false;
            }
            if (StateClosureCount == 0)
            {
                if (!NewMetastate.ReachableStates.Contains(Ori))
                {
                    NewMetastate.ReachableStates.Add(Ori);
                }
                foreach (State s in NewMetastate.ReachableStates)
                    NewMetastate.MKey += s.ID.ToString();
                return true;
            }
            else
            {                
                tmplist.Sort();
                foreach (string st in tmplist)
                    NewMetastate.MKey += st;
 
                NewMetastate.DefineCycle();
                NewMetastate.DefineDead();

                return false;
            }


        }

        public bool BuildOG()
        {
            Stack<OGMeta_state> MetastateStack = new Stack<OGMeta_state>();
            //Stack<OGMeta_state> StoreMetastateStack = new Stack<OGMeta_state>();
            HashSet<string> GeneratedMetastatesKey = new HashSet<string>(); //new
            HashSet<string> GenerateOGTransitionKey = new HashSet<string>();
            List<string> tmplist = new List<string>();
            List<string> Obtifvisited = new List<string>();

            OGMeta_state TmpMetastate1 = new OGMeta_state();
            OGMeta_state TmpMetastate2 = new OGMeta_state();
            OGMeta_state TmpmarkMetastate = null;
            OGTransition TmpOGtransition = new OGTransition();
            State Tmpstate;
            bool ifnew = true;
            bool ifsameobs = false;
            int CountM = 1;
            

            MetastateStack.Push(this.InitialMetaState);
            //StoreMetastateStack.Push(this.InitialMetaState);
            GeneratedMetastatesKey.Add(InitialMetaState.MKey);

            do
            {
                TmpMetastate1 = MetastateStack.Pop();
             
                foreach (Transition obs in TmpMetastate1.OutgoingTransitions)
                {
                    if (!Obtifvisited.Contains(obs.FromState.ID + obs.Event.BaseName + obs.ToState.ID))
                        Obtifvisited.Add(obs.FromState.ID + obs.Event.BaseName + obs.ToState.ID);
                    else
                        continue;

                    tmplist.Clear();
                    ifsameobs = false;
                    Tmpstate = obs.ToState;
                    TmpMetastate2.ID = (CountM++).ToString(); //new
                    if (GenerateReachableState(ref TmpMetastate2, Tmpstate))
                    {
                        TmpMetastate2.DefineCycle();
                        TmpMetastate2.DefineDead();
                    }
                    TmpMetastate2.MKey = TmpMetastate2.MKey + TmpMetastate2.IfCycle + TmpMetastate2.IfDead;

                    if (TmpMetastate1.MKey == TmpMetastate2.MKey)
                    {
                        TmpOGtransition = new OGTransition();
                        TmpOGtransition.practical_transition = obs;
                        TmpOGtransition.FromMstate = TmpMetastate1;
                        TmpOGtransition.ToMstate = TmpMetastate2;
                        TmpOGtransition.OGTKey = obs.Event.ToString() + TmpMetastate1.MKey + TmpMetastate2.MKey;
                        TmpMetastate1.OGOutgoingTransitions.Add(TmpOGtransition);
                        if (!GenerateOGTransitionKey.Contains(TmpOGtransition.OGTKey))
                        {
                            this.OGTranstions.Add(TmpOGtransition);
                        }
                        GenerateOGTransitionKey.Add(TmpOGtransition.OGTKey);
                        continue;
                    }
                    
                    /*****judge if a new Meta states***use string hashset*/
                    foreach (OGTransition ogt in OGTranstions)
                    {
                        if (obs.Event.BaseName.ToString() == ogt.practical_transition.Event.BaseName.ToString() && String.Equals(TmpMetastate1.MKey, ogt.FromMstate.MKey))
                        {
                            ifsameobs = true;
                            ifnew = true;
                            TmpmarkMetastate = ogt.ToMstate;
                            goto label;
                        }

                    }
                    if (GeneratedMetastatesKey.Contains(TmpMetastate2.MKey))
                    {
                        ifnew = false;
                    }
                    else
                    {
                        ifnew = true;
                        
                    }
                    /***********************************/
                label:
                    if (ifnew)
                    {
                        if (ifsameobs == false)
                        {
                            TmpOGtransition = new OGTransition();
                            TmpOGtransition.practical_transition = obs;
                            TmpOGtransition.FromMstate = TmpMetastate1;
                            TmpOGtransition.ToMstate = TmpMetastate2;
                            TmpOGtransition.OGTKey = obs.Event.ToString() + TmpMetastate1.MKey + TmpMetastate2.MKey;
                            TmpMetastate1.OGOutgoingTransitions.Add(TmpOGtransition);

                            this.MetaStates.Add(TmpMetastate2);
                            if(!GenerateOGTransitionKey.Contains(TmpOGtransition.OGTKey))
                            {
                                this.OGTranstions.Add(TmpOGtransition);
                            }
                            GenerateOGTransitionKey.Add(TmpOGtransition.OGTKey);
                            GeneratedMetastatesKey.Add(TmpMetastate2.MKey);
                            MetastateStack.Push(TmpMetastate2);
                        }
                        else
                        {
                            foreach (State s in TmpmarkMetastate.ReachableStates)
                                tmplist.Add(s.ID);
                            foreach (State s in TmpMetastate2.ReachableStates)
                            {
                                if (!TmpmarkMetastate.ReachableStates.Contains(s))
                                {
                                    TmpmarkMetastate.ReachableStates.Add(s);
                                    tmplist.Add(s.ID);
                                }
                            }
                            foreach (Transition t in TmpMetastate2.OutgoingTransitions)
                                TmpmarkMetastate.OutgoingTransitions.Add(t);
                            if (TmpmarkMetastate.IfCycle || TmpMetastate2.IfCycle)
                                TmpmarkMetastate.IfCycle = true;
                            if (TmpmarkMetastate.IfDead || TmpMetastate2.IfDead)
                                TmpmarkMetastate.IfDead = true;

                            GeneratedMetastatesKey.Remove(TmpmarkMetastate.MKey);
                            TmpmarkMetastate.MKey = null;
                            tmplist.Sort();
                            foreach (string s in tmplist)
                                TmpmarkMetastate.MKey += s;
                            TmpmarkMetastate.MKey += TmpmarkMetastate.IfCycle.ToString();
                            TmpmarkMetastate.MKey += TmpmarkMetastate.IfDead.ToString();

                            if (!GeneratedMetastatesKey.Contains(TmpmarkMetastate.MKey))
                            {
                                GeneratedMetastatesKey.Add(TmpmarkMetastate.MKey);
                                foreach (OGTransition o in this.OGTranstions)
                                {
                                    if (o.ToMstate == TmpmarkMetastate)
                                        o.OGTKey = o.practical_transition.Event.ToString() + o.FromMstate.MKey + o.ToMstate.MKey;
                                    break;
                                }
                            }
                            else
                            {
                                bool dupmark = false;
                                OGTransition tmpdupmark = null;
                                foreach (OGTransition o in this.OGTranstions)
                                {
                                    if (o.ToMstate.MKey.Equals(TmpmarkMetastate.MKey) && !o.FromMstate.MKey.Equals(TmpMetastate1.MKey))
                                    {
                                        dupmark = true;
                                        tmpdupmark = o;
                                        break;
                                    }
                                }

                                this.MetaStates.Remove(TmpmarkMetastate);

                                /***Maybe should not delete the transition, but judge if their from state is different, if different, just modify the transition***/
                                foreach (OGTransition o in TmpMetastate1.OGOutgoingTransitions)
                                {
                                    if (o.ToMstate == TmpmarkMetastate)
                                    {
                                        if (dupmark == false)
                                        {
                                            o.ToMstate = o.FromMstate;
                                        }
                                        else
                                        {
                                            o.ToMstate = tmpdupmark.ToMstate;

                                        }
                                        o.OGTKey = o.practical_transition.Event.ToString()+o.FromMstate.MKey+o.ToMstate.MKey;
                                        break;
                                    }
                                }
                                //foreach (OGTransition o in this.OGTranstions)
                                //{
                                //    if (o.ToMstate == TmpmarkMetastate)
                                //    {
                                //        if (dupmark == false)
                                //            this.OGTranstions.Remove(o);
                                //        else
                                //        {
                                //            o.ToMstate = tmpdupmark.ToMstate;
                                //            o.OGTKey = o.practical_transition.Event.ToString()+o.FromMstate.MKey+o.ToMstate.MKey;
                                //        }
                                //        break;
                                //    }
                                //}

                                if (MetastateStack.Peek() == TmpmarkMetastate)
                                    MetastateStack.Pop();
                                else
                                {
                                    int i = 0;
                                    List<OGMeta_state> l = MetastateStack.ToList();
                                    l.Remove(TmpmarkMetastate);
                                    OGMeta_state[] tl = new OGMeta_state[l.Count];
                                    foreach (OGMeta_state o in l)
                                    {
                                        tl[i] = o;
                                        i++;
                                    }
                                    MetastateStack.Clear();
                                    for (i = tl.Length - 1; i >= 0; i++)
                                    {
                                        MetastateStack.Push(tl[i]);
                                    }
                                    //copy metastatestack to another array and delete that one
                                }

                            }
                        }
                    
                    }
                    else
                        CountM--;

                    TmpMetastate2 = new OGMeta_state();
                }
            }while(MetastateStack.Count>0);

            return true;
        }

        public void InitMetastate()
        {
            this.InitialMetaState.ID = "0";
            if (GenerateReachableState(ref InitialMetaState, graph.InitialState))
            {
                this.InitialMetaState.DefineCycle();
                this.InitialMetaState.DefineDead();
            }
            this.InitialMetaState.MKey = this.InitialMetaState.MKey + this.InitialMetaState.IfCycle + this.InitialMetaState.IfDead;
        }

        public void GenerateObsSet(BuchiAutomata OGBA, List<string> synlist)
        {
            List<string> Ename = new List<string>();   
            foreach (PAT.Common.Classes.BA.Transition trans in OGBA.Transitions)
            {
                foreach (Proposition label in trans.labels)
                {
                    string labelstring = label.Label;

                    PAT.Common.Classes.Expressions.ExpressionClass.Expression exp;

                    if (!(OGBA.DeclarationDatabase.TryGetValue(labelstring, out exp))) //just get event name?
                    {
                        if(!Ename.Contains(labelstring))
                            Ename.Add(labelstring);
                    }

                }
            }
            foreach (Transition t in graph.Transitions)
            {
                if (Ename.Contains(t.Event.ToString()))
                {
                    OBs.Add(t.Event.ToString());
                }
            }

            foreach (string e in synlist)
            {
                if(!(OBs.Contains(e.ToString())))
                {                   
                    OBs.Add(e);
                }
            }

            //for test,will delete in normal version
           // OBs.Add("obs");
            //OBs.Add("sync");
        }

    }


    /********for modular og**********************/
    public class SynOGMetastate
    {
        public KeyValuePair<OGMeta_state, OGMeta_state> SynMeta_state; //basement two modular,!!NEED EXPEND!!
        //public List<OGMeta_state> SynMeta_state //realistic status
        public bool SynIfcycle;
        public bool SynIfdead;
        public List<OGTransition> InputTransition;

        public string ID;

        public SynOGMetastate()
        {
            //SynMeta_state = new KeyValuePair<OGMeta_state, OGMeta_state>();
            InputTransition = new List<OGTransition>();
            SynIfcycle = false;
            SynIfdead = false;
            ID = "";
        }

        public void SynDefineCycle()
        {
            bool ifcycle1;
            bool ifcycle2;
            ifcycle1 = this.SynMeta_state.Key.IfCycle;
            ifcycle2 = this.SynMeta_state.Value.IfCycle;

            if(ifcycle1 || ifcycle2)
            {
                this.SynIfcycle = true;
            }
            else
            {
                this.SynIfcycle = false;
            }
        }

        public bool SynDefineDead(List<string> synlist)  //
        {
            OGMeta_state[] M = new OGMeta_state[2];
            List<string>[] TmpEnable = new List<string>[2];
            List<string> TmpSEnable = new List<string>();
            
            IEnumerable<string>[] sync = new List<string>[2];
            IEnumerable<string> Unionlist = new List<string>();

            IEnumerable<string> TmpE = new List<string>(); //mark subset of syn

            bool[] ifdead = new bool[2];
            //int markcount = 0; //for the final condition
            int i;

            M[0] = this.SynMeta_state.Key;
            M[1] = this.SynMeta_state.Value;

            ifdead[0] = M[0].IfDead;
            ifdead[1] = M[1].IfDead;

            sync[0] = new List<string>();
            sync[1] = new List<string>();
            
            if (ifdead[0] && ifdead[1])
            {
                this.SynIfdead = true;
                return true;
            }

            for(i=0;i<2;i++)
            {
                TmpEnable[i] = new List<string>();
                foreach (Transition t in M[i].OutgoingTransitions)
                {               
                    TmpEnable[i].Add(t.Event.ToString());
                }
            }

            //second condition
            for (i=0;i<2;i++)
            {
                if(ifdead[i] == false)
                {
                    TmpE = synlist.Except(TmpEnable[1-i],StringComparer.OrdinalIgnoreCase);
                    foreach (State s in M[i].ReachableStates)
                    {
                        foreach (Transition ss in s.OutgoingTransitions)
                        {
                            TmpSEnable.Add(ss.Event.ToString());
                        }
                        if(TmpSEnable.Intersect(TmpE).Count() != 0)
                        {
                            if(TmpSEnable.Except(TmpE,StringComparer.OrdinalIgnoreCase).Count() == 0)
                            {
                                ifdead[i] = true;
                                break;
                            }
                        }
                        TmpSEnable = new List<string>();
                    }
                }
            }

            TmpSEnable = new List<string>();
            if (ifdead[0] && ifdead[1])
            {
                this.SynIfdead = true;
                return true;
            }

            //third condition
            for (i=0;i<2;i++)
            {
                if(ifdead[i] && !ifdead[1-i])
                {
                    foreach (State ss in M[1-i].ReachableStates)
                    {
                        foreach (Transition t in ss.OutgoingTransitions)
                        {
                            TmpSEnable.Add(t.Event.ToString());
                        }
                        if(TmpSEnable.Intersect(synlist).Count() != 0)
                        {
                            if(TmpSEnable.Except(synlist,StringComparer.OrdinalIgnoreCase).Count() == 0)
                            {
                                this.SynIfdead = true;
                                return true;
                            }
                        }
                    }
                }
            }

            //final condition
            int Scount = 0;
            IEnumerable<string> TmpUnion = new List<string>();
            List<string> TmpAvai = new List<string>();
            List<State> TmpState = new List<State>();

            Unionlist = TmpEnable[0].Intersect(TmpEnable[1]);
            for (i=0;i<2;i++)
            {
                sync[i] = synlist.Intersect(TmpEnable[i]);

                if(TmpEnable[1-i].Intersect(sync[i]).Count() != 0)
                {
                    if(sync[i].Except(TmpEnable[1-i]).Count() != 0)
                    {
                        TmpUnion = sync[i].Except(TmpEnable[1-i],StringComparer.OrdinalIgnoreCase);
                        sync[i] = sync[i].Except(TmpUnion,StringComparer.OrdinalIgnoreCase);
                    }  

                    foreach (State s in M[1-i].ReachableStates)
                    {
                        foreach (Transition t in s.OutgoingTransitions)
                        {
                            if(sync[i].Contains(t.Event.ToString()))
                            {
                                Scount++;
                            }
                        }
                        if (Scount == s.OutgoingTransitions.Count)
                            TmpState.Add(s);

                        Scount = 0;
                    }

                    if(TmpState.Count == 0)
                    {
                        this.SynIfdead = false;
                        return false;
                    }
                    else
                    {
                        foreach (State ss in TmpState)
                        {
                            foreach(Transition tt in ss.OutgoingTransitions)
                            {
                                TmpAvai.Add(tt.Event.ToString());
                            }
                        }
                        sync[i] = sync[i].Intersect(TmpAvai);
                    }
                }
                else
                {
                    this.SynIfdead = false;
                    return false;
                }

            }           
            if(sync[0].Intersect(sync[1]).Count() == 0)
            {
                this.SynIfdead = true;
                return true;
            }

            return false;
        }
    }

    public class SynOG
    {
        public Dictionary<string, SynOGMetastate> SynOGMetastates;
        public SynOGMetastate InitialSynOGMetastate;
        public List<OGTransition> SynOBTransitions;
        public List<string> SynEvents;

        public Dictionary<string, ModularOG> AllModularOGs;

        public Dictionary<string, Automaton> AllModularLTS; //Basement

        public SynOG()
        {
            SynOGMetastates = new Dictionary<string, SynOGMetastate>();
            //InitialSynOGMetastate = new KeyValuePair<OGMeta_state,OGMeta_state>();
            InitialSynOGMetastate = new SynOGMetastate();
            SynOBTransitions = new List<OGTransition>();
            SynEvents = new List<string>();
            AllModularOGs = new Dictionary<string, ModularOG>();

            AllModularLTS = new Dictionary<string, Automaton>();
        }

        public void AddModularOG(ModularOG MOG)
        {
            AllModularOGs.Add(MOG.ID, MOG);
        }

        //BASEMENT
        public void AddModularLTS(Automaton MLTS)
        {
            AllModularLTS.Add(MLTS.Name, MLTS);
        }


        public void GenerateSynEvent()
        {
            Stack<List<string>> LTSEvents = new Stack<List<string>>();
            List<string> MLTSEvents;
            List<string> Tmplist;
            IEnumerable<string> Unionlist = new List<string>();
            bool mark = false;

            if (AllModularLTS.Count > 1)
            {
                foreach (KeyValuePair<string, Automaton> mlts in AllModularLTS)
                {
                    MLTSEvents = new List<string>();
                    foreach (Transition e in mlts.Value.Transitions)
                    {
                        if (!MLTSEvents.Contains(e.Event.ToString()))
                        {
                            MLTSEvents.Add(e.Event.ToString());
                        }
                    }
                    LTSEvents.Push(MLTSEvents);
                    MLTSEvents = new List<string>();
                }

                MLTSEvents = LTSEvents.Pop();
                do
                {
                    Tmplist = LTSEvents.Pop();
                    if (!mark)
                    {
                        Unionlist = MLTSEvents.Intersect(Tmplist);
                        mark = true;
                    }
                    else
                    {
                        Unionlist = Unionlist.Intersect(Tmplist);
                    }
                } while (LTSEvents.Count > 0);

                foreach (string e in Unionlist)
                {
                    this.SynEvents.Add(e);
                }
            }
            else
            {
                foreach (KeyValuePair<string, Automaton> mlts in AllModularLTS)
                    foreach (Transition e in mlts.Value.Transitions)
                        if (e.Event.BaseName.ToString() == "sync")
                            this.SynEvents.Add(e.ToString());
            }
        }

        public int BuildSynOG(string M1, string M2)
        {
            ModularOG MOG1;
            ModularOG MOG2;
            OGMeta_state Mstate1;
            OGMeta_state Mstate2;
          
            SynOGMetastate SOGM = new SynOGMetastate();
            OGTransition SOGT = new OGTransition();
            Stack<SynOGMetastate> Todo = new Stack<SynOGMetastate>();
            //int Count = 0;
            bool judge = false;

            AllModularOGs.TryGetValue(M1, out MOG1);
            AllModularOGs.TryGetValue(M2, out MOG2);
            InitialSynOGMetastate.SynMeta_state = new KeyValuePair<OGMeta_state, OGMeta_state>(MOG1.InitialMetaState, MOG2.InitialMetaState);
            InitialSynOGMetastate.ID = MOG1.InitialMetaState.MKey + MOG2.InitialMetaState.MKey;

            if (MOG1.InitialMetaState.OGOutgoingTransitions.Count == 0 && MOG2.InitialMetaState.OGOutgoingTransitions.Count == 0)
            {
                return 0;
            }
            else if (MOG1.InitialMetaState.OGOutgoingTransitions.Count == 0 && MOG2.InitialMetaState.OGOutgoingTransitions.Count != 0)
            {
                foreach (OGTransition MOGT2 in MOG2.InitialMetaState.OGOutgoingTransitions)
                {
                    SOGM.SynMeta_state = new KeyValuePair<OGMeta_state, OGMeta_state>(MOG1.InitialMetaState, MOGT2.ToMstate);


                    SOGT.practical_transition = MOGT2.practical_transition;
                    SOGT.FromSynMstate = InitialSynOGMetastate.ID;
                    SOGM.ID = MOG1.InitialMetaState.MKey + MOGT2.ToMstate.MKey;
                    SOGT.ToSynMstate = SOGM.ID;

                    SOGM.InputTransition.Add(SOGT);
                    SOGM.SynDefineCycle();
                    SOGM.SynDefineDead(SynEvents);
                   

                    if (!SynOGMetastates.ContainsKey(SOGM.ID))
                    {
                        SynOGMetastates.Add(SOGM.ID, SOGM);
                        Todo.Push(SOGM);
                    }
                    if(!SynOBTransitions.Contains(SOGT))
                        SynOBTransitions.Add(SOGT);

                    SOGM = new SynOGMetastate();
                    SOGT = new OGTransition();
                }
                goto label;
            }
            else
            {
                foreach (OGTransition MOGT1 in MOG1.InitialMetaState.OGOutgoingTransitions)
                {
                    SOGM.SynMeta_state = new KeyValuePair<OGMeta_state, OGMeta_state>(MOGT1.ToMstate, MOG2.InitialMetaState);
                    SOGM.ID = MOGT1.ToMstate.MKey + MOG2.InitialMetaState.MKey;

                    SOGT.practical_transition = MOGT1.practical_transition;
                    SOGT.FromSynMstate = InitialSynOGMetastate.ID;
                   
                    SOGT.ToSynMstate = SOGM.ID;

                    SOGM.InputTransition.Add(SOGT);
                    SOGM.SynDefineCycle();
                    SOGM.SynDefineDead(SynEvents);
                   

                    if (!SynOGMetastates.ContainsKey(SOGM.ID))
                    {
                        SynOGMetastates.Add(SOGM.ID, SOGM);
                        Todo.Push(SOGM);
                    }

                    if (!SynOBTransitions.Contains(SOGT))
                        SynOBTransitions.Add(SOGT);

                    SOGM = new SynOGMetastate();
                    SOGT = new OGTransition();
                }
                goto label;
            }

            //Initial step
            foreach (OGTransition MOGT1 in MOG1.InitialMetaState.OGOutgoingTransitions)
            {
                //SynOBTransitions.Add(MOGT1);
                foreach (OGTransition MOGT2 in MOG2.InitialMetaState.OGOutgoingTransitions)
                {
                    if (MOGT2.practical_transition.Event.ToString() == MOGT1.practical_transition.Event.ToString())
                    {
                        SOGM.SynMeta_state = new KeyValuePair<OGMeta_state, OGMeta_state>(MOGT1.ToMstate, MOGT2.ToMstate);
                        SOGM.ID = MOGT1.ToMstate.MKey + MOGT2.ToMstate.MKey;
                        judge = true;
                    }
                    else
                    {
                        SOGM.SynMeta_state = new KeyValuePair<OGMeta_state, OGMeta_state>(MOGT1.ToMstate, MOG2.InitialMetaState);
                        SOGM.ID = MOGT1.ToMstate.MKey + MOG2.InitialMetaState.MKey;
                    }

                    SOGT.practical_transition = MOGT1.practical_transition;
                    SOGT.FromSynMstate = InitialSynOGMetastate.ID;
                    SOGT.ToSynMstate = SOGM.ID;

                    SOGM.InputTransition.Add(SOGT);
                    SOGM.SynDefineCycle();
                    SOGM.SynDefineDead(SynEvents);

                    if (!SynOGMetastates.ContainsKey(SOGM.ID))
                    {
                        SynOGMetastates.Add(SOGM.ID, SOGM);
                        Todo.Push(SOGM);
                    }
                    if (!SynOBTransitions.Contains(SOGT))
                        SynOBTransitions.Add(SOGT);

                    SOGM = new SynOGMetastate();
                    SOGT = new OGTransition();

                    if (!judge)
                    {
                        SOGM.SynMeta_state = new KeyValuePair<OGMeta_state, OGMeta_state>(MOG1.InitialMetaState, MOGT2.ToMstate);
                        SOGM.ID = MOG1.InitialMetaState.MKey + MOGT2.ToMstate.MKey;

                        SOGT.practical_transition = MOGT2.practical_transition;
                        SOGT.FromSynMstate = InitialSynOGMetastate.ID;
                        SOGT.ToSynMstate = SOGM.ID;

                        SOGM.InputTransition.Add(SOGT);
                        SOGM.SynDefineCycle();
                        SOGM.SynDefineDead(SynEvents);

                        if (!SynOGMetastates.ContainsKey(SOGM.ID))
                        {
                            SynOGMetastates.Add(SOGM.ID, SOGM);
                            Todo.Push(SOGM);
                        }

                        if (!SynOBTransitions.Contains(SOGT))
                            SynOBTransitions.Add(SOGT);

                        SOGM = new SynOGMetastate();
                        SOGT = new OGTransition();
                    }
                }
            }

label:
            judge = false;
            SynOGMetastate SOGM2 = new SynOGMetastate();
            //following product.
            do
            {
                if (Todo.Count != 0)
                    SOGM = Todo.Pop();
                else
                    break;
                Mstate1 = SOGM.SynMeta_state.Key;
                Mstate2 = SOGM.SynMeta_state.Value;

                if (Mstate1.OGOutgoingTransitions.Count == 0 && Mstate2.OGOutgoingTransitions.Count == 0)
                {
                    continue;
                }
                if (Mstate1.OGOutgoingTransitions.Count == 0 && Mstate2.OGOutgoingTransitions.Count != 0)
                {
                    foreach (OGTransition MOGT2 in Mstate2.OGOutgoingTransitions)
                    {
                        SOGM2.SynMeta_state = new KeyValuePair<OGMeta_state, OGMeta_state>(Mstate1, MOGT2.ToMstate);
                        SOGM2.ID = Mstate1.MKey + MOGT2.ToMstate.MKey;

                        SOGT.practical_transition = MOGT2.practical_transition;
                        SOGT.FromSynMstate = SOGM.ID;
                        SOGT.ToSynMstate = SOGM2.ID;

                        SOGM2.InputTransition.Add(SOGT);
                        SOGM2.SynDefineCycle();
                        SOGM2.SynDefineDead(SynEvents);

                        if (!SynOGMetastates.ContainsKey(SOGM.ID))
                        {
                            SynOGMetastates.Add(SOGM2.ID, SOGM2);
                            Todo.Push(SOGM2);
                        }

                        if (!SynOBTransitions.Contains(SOGT))
                            SynOBTransitions.Add(SOGT);

                        SOGM2 = new SynOGMetastate();
                        SOGT = new OGTransition();
                    }
                    continue;
                }
                if (Mstate2.OGOutgoingTransitions.Count == 0 && Mstate1.OGOutgoingTransitions.Count != 0)
                {
                    foreach (OGTransition MOGT1 in Mstate1.OGOutgoingTransitions)
                    {
                        SOGM2.SynMeta_state = new KeyValuePair<OGMeta_state, OGMeta_state>(MOGT1.ToMstate, Mstate2);
                        SOGM2.ID = Mstate1.MKey + MOGT1.ToMstate.MKey;

                        SOGT.practical_transition = MOGT1.practical_transition;
                        SOGT.FromSynMstate = SOGM.ID;
                        SOGT.ToSynMstate = SOGM2.ID;

                        SOGM2.InputTransition.Add(SOGT);
                        SOGM2.SynDefineCycle();
                        SOGM2.SynDefineDead(SynEvents);

                        if (!SynOGMetastates.ContainsKey(SOGM.ID))
                        {
                            SynOGMetastates.Add(SOGM2.ID, SOGM2);
                            Todo.Push(SOGM2);
                        }

                        if (!SynOBTransitions.Contains(SOGT))
                            SynOBTransitions.Add(SOGT);

                        SOGM2 = new SynOGMetastate();
                        SOGT = new OGTransition();
                    }
                    continue;
                }

                foreach (OGTransition MOGT1 in Mstate1.OGOutgoingTransitions)
                {
                    foreach (OGTransition MOGT2 in Mstate2.OGOutgoingTransitions)
                    {
                        if (MOGT2.practical_transition.Event.ToString() == MOGT1.practical_transition.Event.ToString())
                        {
                            SOGM2.SynMeta_state = new KeyValuePair<OGMeta_state, OGMeta_state>(MOGT1.ToMstate, MOGT2.ToMstate);
                            SOGM2.ID = MOGT1.ToMstate.MKey + MOGT2.ToMstate.MKey;
                            judge = true;
                        }
                        else
                        {
                            SOGM2.SynMeta_state = new KeyValuePair<OGMeta_state, OGMeta_state>(MOGT1.ToMstate, Mstate2);
                            SOGM2.ID = MOGT1.ToMstate.MKey + Mstate2.MKey;
                        }

                        SOGT.practical_transition = MOGT1.practical_transition;
                        SOGT.FromSynMstate = SOGM.ID;
                        SOGT.ToSynMstate = SOGM2.ID;

                        SOGM2.InputTransition.Add(SOGT);
                        SOGM2.SynDefineCycle();
                        SOGM2.SynDefineDead(SynEvents);


                        if (!SynOGMetastates.ContainsKey(SOGM.ID))
                        {
                            SynOGMetastates.Add(SOGM2.ID, SOGM2);
                            Todo.Push(SOGM2);
                        }

                        if (!SynOBTransitions.Contains(SOGT))
                            SynOBTransitions.Add(SOGT);

                        SOGM2 = new SynOGMetastate();
                        SOGT = new OGTransition();

                        if (!judge)
                        {
                            SOGM2.SynMeta_state = new KeyValuePair<OGMeta_state, OGMeta_state>(Mstate1, MOGT2.ToMstate);
                            SOGM2.ID = Mstate1.MKey + MOGT2.ToMstate.MKey;

                            SOGT.practical_transition = MOGT2.practical_transition;
                            SOGT.FromSynMstate = SOGM.ID;
                            SOGT.ToSynMstate = SOGM2.ID;

                            SOGM2.InputTransition.Add(SOGT);
                            SOGM2.SynDefineCycle();
                            SOGM2.SynDefineDead(SynEvents);

                            if (!SynOGMetastates.ContainsKey(SOGM.ID))
                            {
                                SynOGMetastates.Add(SOGM2.ID, SOGM2);
                                Todo.Push(SOGM2);
                            }

                            if (!SynOBTransitions.Contains(SOGT))
                                SynOBTransitions.Add(SOGT);

                            SOGM2 = new SynOGMetastate();
                            SOGT = new OGTransition();
                        }
                    }
                }

            } while (Todo.Count > 0);
            return 1;
        }


    }

    public partial class TAAssertionLTL
    {
        public SynOG SynOBGraph;
        public Automaton AbstractLTS;
        public PAT.CLTS.LTS.Monolithic.Automata AbstractProcess;
        public ModularOG[] ObservationGraph;
        

        public void ModularLTS2SynOG()
        {
        //    //ObservationGraph = new OG();
            int i=0;
            SynOBGraph = new SynOG();
            ObservationGraph = new ModularOG[Process.Processes.Count];
            int count = 0;

            Automaton[] LTSlist = new Automaton[Process.Processes.Count];
            foreach (Automaton a in Process.Processes)
            {
                LTSlist[i] = a;
                SynOBGraph.AddModularLTS(a);
                i++;
            }

            SynOBGraph.GenerateSynEvent();

        //    /***FOR TESTING,MAUNAL GENERATE LTS***/
            
            while (SynOBGraph.AllModularLTS.Count > count)
            {
                ObservationGraph[count] = new ModularOG(LTSlist[count]);  //must get graph from pat
                ObservationGraph[count].GenerateObsSet(BA, SynOBGraph.SynEvents);
                ObservationGraph[count].InitMetastate();
                ObservationGraph[count].BuildOG();
                ObservationGraph[count].ID = count.ToString();
                SynOBGraph.AddModularOG(ObservationGraph[count]);
                count++;
            }

            //basement, suppose two modulars
            SynOBGraph.BuildSynOG(ObservationGraph[0].ID, ObservationGraph[1].ID);
            List<string> var = new List<string>();
            i=0;
 
            SynOGMetastate initsm = SynOBGraph.InitialSynOGMetastate;
            OGMeta_state tmpm1 = initsm.SynMeta_state.Key;
            OGMeta_state tmpm2 = initsm.SynMeta_state.Value;
            State Absinitstate = new State("State"+i.ToString(), initsm.ID, false, false);
            i++;

            Absinitstate.cdead = initsm.SynIfdead;
            Absinitstate.cloop = initsm.SynIfcycle;

            State AbsState1=null;
            State AbsState2=null;
            Transition Abstransition;
            List<State> Absstates = new List<State>();
            List<Transition> Abstransitions = new List<Transition>();
            foreach (OGTransition ogt in SynOBGraph.SynOBTransitions)
            {
                Abstransition = ogt.practical_transition;
                if (SynOBGraph.SynOGMetastates[ogt.FromSynMstate].ID != initsm.ID)
                {
                    AbsState1 = new State("State" + i.ToString(), SynOBGraph.SynOGMetastates[ogt.FromSynMstate].ID, false, false);
                    AbsState1.cdead = SynOBGraph.SynOGMetastates[ogt.FromSynMstate].SynIfdead;
                    AbsState1.cloop = SynOBGraph.SynOGMetastates[ogt.FromSynMstate].SynIfcycle;
                    i++;
                    Abstransition.FromState = AbsState1;
                }
                else
                    Abstransition.FromState = Absinitstate;

                if (SynOBGraph.SynOGMetastates[ogt.ToSynMstate].ID != initsm.ID)
                {
                    AbsState2 = new State("State" + i.ToString(), SynOBGraph.SynOGMetastates[ogt.ToSynMstate].ID, false, false);
                    AbsState2.cdead = SynOBGraph.SynOGMetastates[ogt.ToSynMstate].SynIfdead;
                    AbsState2.cloop = SynOBGraph.SynOGMetastates[ogt.ToSynMstate].SynIfcycle;
                    i++;
                    Abstransition.ToState = AbsState2;
                }
                else
                    Abstransition.ToState = Absinitstate;

                if (SynOBGraph.SynOGMetastates[ogt.FromSynMstate].ID != initsm.ID)
                {
                    AbsState1.OutgoingTransitions.Add(Abstransition);
                }
                else
                    Absinitstate.OutgoingTransitions.Add(Abstransition);

                if (!Absstates.Contains(AbsState1) && AbsState1!=null)
                    Absstates.Add(AbsState1);
                if(!Absstates.Contains(AbsState2) && AbsState2!=null)
                    Absstates.Add(AbsState2);
                
                Abstransitions.Add(Abstransition);
            }
            Absstates.Add(Absinitstate);
            AbstractLTS = new Automaton(Process.ProcessName, var, Absstates);

            foreach (Transition t in Abstransitions)
            {
                if (!AbstractLTS.EventList.Contains(t.Event.ToString()))
                    AbstractLTS.EventList.Add(t.Event.ToString());
            }

            AbstractLTS.InitialState = Absinitstate;

            List<string> AbstractParameters = new List<string>();
            foreach (Automaton a in Process.Processes)
            {
                AbstractParameters = AbstractParameters.Union(a.Parameters).ToList();
            }

            AbstractLTS.Parameters = AbstractParameters;
            AbstractLTS.StateNumber = Absstates.Count;
            AbstractLTS.TransitionNumber = Absstates.Count;

            AbstractProcess.Processes.Add(AbstractLTS);
            AbstractProcess.ProcessName = Process.ProcessName;
            OGInitStep = new Configuration(AbstractProcess, Constants.INITIAL_EVENT, null, InitialStep.GlobalEnv);
            
        }

        /*Comments: Based on the original LTL verfication function in PAT, I know the on-the-fly product between BA and LTS is based on the specific Makeonemove in object BA.
         * Now, if I want to use OG to do verfication, I need to initialize Configuration object with OG syn-Metastate. e.g.like Configurationbase initstep = new LTSConfiguration(..)
         * I read the structure of LTSConfiguration,LTSBase and Configurationbase, DefinitionRef,Definition, I am puzzled how I can utilize these classes. In my mind, I need to implement my
         * own classes to reach the function of these classes. I really appreciate your instructions.*/



        private void OGVerification()   //on-the-fly OG verfication based on tarjan verfication in LTS, I don't know how to integrate OG in this part.
        {
            ////LY: Process is the automata, which will give you everything you need.
            ////this.Process

            ////LY: InitialStep is the initial configuration to start with
            //// InitialStep = new Configuration(Process, Constants.INITIAL_EVENT, null, GlobalEnv);
            VerificationOutput.CounterExampleTrace = null;
            ModularLTS2SynOG();

            //out-going table.           
            Dictionary<string, List<string>> OutgoingTransitionTable = new Dictionary<string, List<string>>(PAT.Common.Classes.Ultility.Ultility.MC_INITIAL_SIZE);

            //DFS Stack
            Stack<KeyValuePair<ConfigurationBase, string>> TaskStack = new Stack<KeyValuePair<ConfigurationBase, string>>(5000);

            //DFS data, which mapping each state to an int[] of size 2, first is the pre-order, second is the lowlink
            StringDictionary<int[]> DFSData = new StringDictionary<int[]>(PAT.Common.Classes.Ultility.Ultility.MC_INITIAL_SIZE);

            List<KeyValuePair<ConfigurationBase, string>> initials = new List<KeyValuePair<ConfigurationBase, string>>();
            HashSet<string> existed = new HashSet<string>();

            foreach (string s in BA.InitialStates)
            {
                List<string> next = BA.MakeOneMove(s, OGInitStep);

                foreach (string var in next)
                {
                    //if (!existed.Contains(var))
                    //{
                    //    existed.Add(var);
                    //    initials.Add(new KeyValuePair<ConfigurationBase, string>(InitialStep, var));
                    //}
                    if (existed.Add(var))
                    {
                        initials.Add(new KeyValuePair<ConfigurationBase, string>(OGInitStep, var));
                    }
                }
            }

            if (initials.Count == 0)
            {
                VerificationOutput.VerificationResult = VerificationResultType.VALID;
                return;
            }

            for (int z = 0; z < initials.Count; z++)
            {
                KeyValuePair<ConfigurationBase, string> initState = initials[z];
                TaskStack.Push(initState);
                string ID = initState.Key.GetIDWithEvent() + Constants.SEPARATOR + initState.Value;
                DFSData.Add(ID, new int[] { VISITED_NOPREORDER, 0 });
                OutgoingTransitionTable.Add(ID, new List<string>(8));
            }

            List<string> StronglyConnectedComponets = new List<string>(1024);
            Stack<KeyValuePair<ConfigurationBase, string>> stepStack = new Stack<KeyValuePair<ConfigurationBase, string>>(1024);

            //# Preorder counter 
            int i = 0;

            //store the expended event step of a node to avoid multiple invocation of the make one move.
            Dictionary<string, List<KeyValuePair<ConfigurationBase, string>>> ExpendedNode = new Dictionary<string, List<KeyValuePair<ConfigurationBase, string>>>(1024);

            do
            {
                if (CancelRequested)
                {
                    VerificationOutput.NoOfStates = DFSData.Count; // VisitedWithID.Count;
                    return;
                }

                KeyValuePair<ConfigurationBase, string> pair = TaskStack.Peek();
                ConfigurationBase config = pair.Key;
                string v = pair.Key.GetIDWithEvent() + Constants.SEPARATOR + pair.Value;
                List<string> outgoing = OutgoingTransitionTable[v];

                int[] nodeData = DFSData.GetContainsKey(v);

                if (nodeData[0] == VISITED_NOPREORDER)
                {
                    nodeData[0] = i;
                    i++;
                }

                bool done = true;

                if (ExpendedNode.ContainsKey(v))
                {
                    List<KeyValuePair<ConfigurationBase, string>> list = ExpendedNode[v];
                    if (list.Count > 0)
                    {
                        //transverse all steps
                        for (int k = list.Count - 1; k >= 0; k--)
                        {
                            KeyValuePair<ConfigurationBase, string> step = list[k];

                            //if the step is a unvisited step
                            string tmp = step.Key.GetIDWithEvent() + Constants.SEPARATOR + step.Value;
                            if (DFSData.GetContainsKey(tmp)[0] == VISITED_NOPREORDER)
                            {
                                if (done)
                                {
                                    TaskStack.Push(step);
                                    done = false;
                                    list.RemoveAt(k);
                                }
                            }
                            else
                            {
                                list.RemoveAt(k);
                            }
                        }
                    }
                }
                else
                {
                    IEnumerable<ConfigurationBase> list = config.MakeOneMove();
                    List<KeyValuePair<ConfigurationBase, string>> product = new List<KeyValuePair<ConfigurationBase, string>>();

                    foreach (ConfigurationBase step in list)
                    {
                        List<string> states = BA.MakeOneMove(pair.Value, step);

                        for (int j = 0; j < states.Count; j++)
                        {
                            product.Add(new KeyValuePair<ConfigurationBase, string>(step, states[j]));
                        }
                    }

                    //count the transitions visited
                    VerificationOutput.Transitions += product.Count;

                    for (int k = product.Count - 1; k >= 0; k--)
                    {
                        KeyValuePair<ConfigurationBase, string> step = product[k];
                        string tmp = step.Key.GetIDWithEvent() + Constants.SEPARATOR + step.Value;
                        int[] data = DFSData.GetContainsKey(tmp);
                        if (data != null)
                        {
                            outgoing.Add(tmp);
                            if (data[0] == VISITED_NOPREORDER)
                            {
                                if (done)
                                {
                                    TaskStack.Push(step);
                                    done = false;
                                    product.RemoveAt(k);
                                }
                                else
                                {
                                    product[k] = step;
                                }
                            }
                            else
                            {
                                product.RemoveAt(k);
                            }
                        }
                        else
                        {
                            DFSData.Add(tmp, new int[] { VISITED_NOPREORDER, 0 });
                            OutgoingTransitionTable.Add(tmp, new List<string>(8));
                            outgoing.Add(tmp);

                            if (done)
                            {
                                TaskStack.Push(step);
                                done = false;
                                product.RemoveAt(k);
                            }
                            else
                            {
                                product[k] = step;
                            }
                        }
                    }

                    ExpendedNode.Add(v, product);
                }

                if (done)
                {
                    int lowlinkV = nodeData[0];
                    int preorderV = lowlinkV;

                    bool selfLoop = false;
                    for (int j = 0; j < outgoing.Count; j++)
                    {
                        string w = outgoing[j];
                        if (w == v)
                        {
                            selfLoop = true;
                        }

                        int[] wdata = DFSData.GetContainsKey(w);
                        if (wdata[0] != SCC_FOUND)
                        {
                            if (wdata[0] > preorderV)
                            {
                                lowlinkV = Math.Min(lowlinkV, wdata[1]);
                            }
                            else
                            {
                                lowlinkV = Math.Min(lowlinkV, wdata[0]);
                            }
                        }
                    }
                    nodeData[1] = lowlinkV;

                    TaskStack.Pop();

                    if (lowlinkV == preorderV)
                    {
                        StronglyConnectedComponets.Add(v);
                        nodeData[0] = SCC_FOUND;

                        //checking for buchi-fair
                        bool BuchiFair = pair.Value.EndsWith(Constants.ACCEPT_STATE);

                        if (stepStack.Count > 0)
                        {
                            KeyValuePair<ConfigurationBase, string> valuePair = stepStack.Peek();
                            string k = valuePair.Key.GetIDWithEvent() + Constants.SEPARATOR + valuePair.Value;

                            while (stepStack.Count > 0 && DFSData.GetContainsKey(k)[0] > preorderV)
                            {
                                stepStack.Pop();
                                StronglyConnectedComponets.Add(k);
                                DFSData.GetContainsKey(k)[0] = SCC_FOUND;

                                if (!BuchiFair && valuePair.Value.EndsWith(Constants.ACCEPT_STATE))
                                {
                                    BuchiFair = true;
                                }

                                if (stepStack.Count > 0)
                                {
                                    valuePair = stepStack.Peek();
                                    k = valuePair.Key.GetIDWithEvent() + Constants.SEPARATOR + valuePair.Value;
                                }
                            }
                        }

                        if (BuchiFair && (config.IsDeadLock || StronglyConnectedComponets.Count > 1 || selfLoop))
                        {
                            VerificationOutput.VerificationResult = VerificationResultType.INVALID;
                            VerificationOutput.NoOfStates = DFSData.Count;

                            while (TaskStack.Count > 0 && TaskStack.Peek().Key.Event != Constants.INITIAL_EVENT)
                            {
                                TaskStack.Pop();
                            }

                            string startID = null;
                            if (TaskStack.Count > 0)
                            {
                                startID = TaskStack.Peek().Key.GetIDWithEvent() + Constants.SEPARATOR +
                                          TaskStack.Peek().Value;
                            }

                            VerificationOutput.CounterExampleTrace = GetConcreteTrace(InitialStep, GetCounterExample(StronglyConnectedComponets, startID, OutgoingTransitionTable));
                            return;
                        }

                        foreach (string componet in StronglyConnectedComponets)
                        {
                            ExpendedNode.Remove(componet);
                        }

                        StronglyConnectedComponets.Clear();
                    }
                    else
                    {
                        stepStack.Push(pair);
                    }
                }
            } while (TaskStack.Count > 0);

            VerificationOutput.VerificationResult = VerificationResultType.VALID;
            VerificationOutput.NoOfStates = DFSData.Count;
            return;
        }
    }
    
}