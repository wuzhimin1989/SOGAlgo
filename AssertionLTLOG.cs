using System;
using System.Collections.Generic;
using System.Collections;
//using System.Reactive.Concurrency;
using System.Linq;
using System.Text;
using System.Threading;
using System.Diagnostics;
using PAT.Common.Classes.BA;
using PAT.Common.Classes.DataStructure;
using PAT.Common.Classes.LTS;
using PAT.Common.Classes.ModuleInterface;
using PAT.Common.Classes.Ultility;
using PAT.Common.Classes.SemanticModels.LTS.SymbolicMCAlgo.LTSEncoding;

namespace PAT.Common.Classes.SemanticModels.LTS.Assertion
{
    /**********************ori code with some updates*************/
    /*public class State
    {
        public List<Transition> OutgoingTransitions;
        //public Stack<Transition> OutgoingTransitions; //new
        public string Name;
        /// <summary>
        /// Integer type
        /// </summary>
        public string ID;
        

        public int IntraID; //NEW

        public List<string> BelongMID;

       
        public int Index;
        public int lowlink;

        public State();
        public State(string name, string id)
        {
            Name = name;
            ID = id;
            Index = -1;
            OutgoingTransitions = new List<Transition>();
        }

        public State ClearConstant(Dictionary<string, Expression> constMapping)
        {

            return new State(Name, ID);
        }

        public override string ToString()
        {
            return Name;
        }
    }
    public class Transition
    {
        public ParallelDefinition[] Selects;
        public Expression GuardCondition;

        public Event Event;

        public Expression ProgramBlock;

        public string[] LocalVariables;

        public State FromState;
        public State ToState;

        //public Transition(Event e, ParallelDefinition[] selects, Expression Guard, Expression assignment, string[] localvar, State from, State to)
        //{
        //    Event = e;
        //    Selects = selects;
        //    ProgramBlock = assignment;
        //    LocalVariables = localvar;
        //    GuardCondition = Guard;
        //    FromState = from;
        //    ToState = to;
        //}
    }

    /******************************************************************************/
    public class OGTransition
    {
        public BDD.Transition practical_transition;
        public OGMeta_state FromMstate;
        public OGMeta_state ToMstate;

        public string FromSynMstate;
        public string ToSynMstate;

        public OGTransition()
        {
            practical_transition = new BDD.Transition();
            FromMstate = new OGMeta_state();
            ToMstate = new OGMeta_state();
        }

         
    }

    /********Class Meta_State****/
    public class OGMeta_state
    {
        public List<BDD.State> ReachableStates;
        public List<BDD.Transition> UobTransitions;
        public List<BDD.Transition> OutgoingTransitions;
        public List<OGTransition> OGOutgoingTransitions;

        public string ID;
        public string MKey; //new

        /****scc****/
        private int Index;
        private Stack<BDD.State> S;

        public bool IfCycle;
        public bool IfDead;

        public OGMeta_state()
        {
            Index = 0;
            
            S = new Stack<BDD.State>();
            ReachableStates = new List<BDD.State>();
            UobTransitions = new List<BDD.Transition>();
            OutgoingTransitions = new List<BDD.Transition>();
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
            
            /*Stack<BDD.State> todo = new Stack<BDD.State>();
            Stack<BDD.State> explored = new Stack<BDD.State>();
            BDD.State tmpexplore1;
            BDD.State tmpexplore2;

            BDD.State[] tmps = new BDD.State[this.ReachableStates.Count];
            foreach (BDD.State s in this.ReachableStates)
            {
                tmps[j] = s;
                j++;
            }

            todo.Push(tmps[0]);
            explored.Push(tmps[0]);
            while (todo.Count > 0)
            {
                tmpexplore1 = todo.Pop();
                foreach (BDD.Transition t in tmpexplore1.OutgoingTransitions)
                {
                    if (!this.UobTransitions.Contains(t))
                    {
                        continue;
                    }
                    else
                    {
                        tmpexplore2 = t.ToState;
                        if (explored.Contains(tmpexplore2))
                        {
                            this.IfCycle = true;
                            return 1;
                        }
                        else
                        {
                            explored.Push(tmpexplore2);
                            todo.Push(tmpexplore2);
                        }

                    }
                }
            }*/
            
            BDD.State tmp1;
            BDD.State tmp2;
            BDD.Transition tmpt;

            Stack<BDD.State> tmpstack = new Stack<BDD.State>(); //
            Stack<BDD.State> explored = new Stack<BDD.State>(); //
            
            List<BDD.State> todo = new List<BDD.State>();
            Dictionary<BDD.State, Stack<BDD.Transition>> outgoingtransition = new Dictionary<BDD.State,Stack<BDD.Transition>>();
            Stack<BDD.Transition> tmpkv;

            foreach (BDD.State m in this.ReachableStates)
            {
                tmpkv =  new Stack<BDD.Transition>();
                for (j = 0; j < m.OutgoingTransitions.Count; j++)
                {
                    tmpkv.Push(m.OutgoingTransitions[j]);
                }
                m.InitIndex();
                outgoingtransition.Add(m,tmpkv);             
            }
            foreach (KeyValuePair<BDD.State,Stack<BDD.Transition>> k in outgoingtransition)
            {
                BDD.State s = k.Key;
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
                                    explored.Push(tmp2);
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
                    //ifscc = IfStrongConnect(s);

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
            foreach (BDD.State s in ReachableStates)
            {
                ifdead = true;
                foreach (BDD.Transition t in s.OutgoingTransitions)  //use hashtable
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
        public BDD.SymbolicLTS graph;  //configbase?
        public OGMeta_state InitialMetaState;
        public List<OGMeta_state> MetaStates;
        //public List<Transition> ObTranstions;  //must be events
        public List<string> OBs;
        public List<OGTransition> OGTranstions;
 
        public Stack<BDD.State> StatesStack;

        public string ID;

        public ModularOG(ref BDD.SymbolicLTS LTSgraph)
        {
            graph = LTSgraph;
            InitialMetaState = new OGMeta_state();
            MetaStates = new List<OGMeta_state>();
            //ObTranstions = new List<Transition>();
            OBs = new List<string>();
            StatesStack = new Stack<BDD.State>();
            OGTranstions = new List<OGTransition>();
        }
        public bool GenerateReachableState(ref OGMeta_state NewMetastate, BDD.State Ori)
        {
            int StateClosureCount = 0;
            BDD.State tmpstate = new BDD.State();
            BDD.State tmpstate2 = new BDD.State();
            List<string> tmplist = new List<string>();

            NewMetastate.ReachableStates.Add(Ori);
            tmplist.Add(Ori.ID);
            Ori.BelongMID.Add(NewMetastate.ID);

            if (Ori.OutgoingTransitions.Count() >= 0)
            {
                foreach (BDD.Transition t in Ori.OutgoingTransitions)
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
                                foreach (BDD.Transition t2 in tmpstate2.OutgoingTransitions) //use event to replace
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
                foreach (BDD.State s in NewMetastate.ReachableStates)
                    NewMetastate.MKey += s.ID.ToString();
                return true;
            }
            else
            {
                /*do
                    {
                        tmpstate = StatesStack.Pop();
                        GenerateReachableState(ref NewMetastate, tmpstate);
                    } while (StatesStack.Count > 0);*/
                //use iterative to replace recrusive

                tmplist.Sort();
                foreach (string st in tmplist)
                    NewMetastate.MKey += st;
                //if (NewMetastate.ReachableStates.Count == 1)
                //{
                //    NewMetastate.IfCycle = false;
                //    NewMetastate.IfDead = false;
                //}

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
            List<string> tmplist = new List<string>();

            OGMeta_state TmpMetastate1 = new OGMeta_state();
            OGMeta_state TmpMetastate2 = new OGMeta_state();
            OGMeta_state TmpmarkMetastate = null;
            OGTransition TmpOGtransition = new OGTransition();
            BDD.State Tmpstate;
            bool ifnew = true;
            bool ifsameobs = false;
            int CountM = 1;
            

            MetastateStack.Push(this.InitialMetaState);
            //StoreMetastateStack.Push(this.InitialMetaState);
            GeneratedMetastatesKey.Add(InitialMetaState.MKey);

            do
            {
                TmpMetastate1 = MetastateStack.Pop();
             
                foreach (BDD.Transition obs in TmpMetastate1.OutgoingTransitions)
                {
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
                    
                    /*****judge if a new Meta states***use string hashset*/
                    if (GeneratedMetastatesKey.Contains(TmpMetastate2.MKey))
                    {
                        ifnew = false;
                    }
                    else
                    {
                        ifnew = true;
                        foreach (OGTransition ogt in OGTranstions)
                        {
                            if (obs.Event.BaseName.ToString() == ogt.practical_transition.Event.BaseName.ToString() && String.Equals(TmpMetastate1.MKey, ogt.FromMstate.MKey))
                            {
                                ifsameobs = true;
                                TmpmarkMetastate = ogt.ToMstate;
                            }
                            
                        }
                    }
                    /***********************************/

                    if (ifnew)
                    {
                        if (ifsameobs == false)
                        {
                            TmpOGtransition.practical_transition = obs;
                            TmpOGtransition.FromMstate = TmpMetastate1;
                            TmpOGtransition.ToMstate = TmpMetastate2;
                            TmpMetastate1.OGOutgoingTransitions.Add(TmpOGtransition);

                            this.MetaStates.Add(TmpMetastate2);
                            if(!this.OGTranstions.Contains(TmpOGtransition))
                            {
                                this.OGTranstions.Add(TmpOGtransition);
                            }
                            GeneratedMetastatesKey.Add(TmpMetastate2.MKey);
                            MetastateStack.Push(TmpMetastate2);
                        }
                        else
                        {
                            foreach (BDD.State s in TmpmarkMetastate.ReachableStates)
                                tmplist.Add(s.ID);
                            foreach (BDD.State s in TmpMetastate2.ReachableStates)
                            {
                                if (!TmpmarkMetastate.ReachableStates.Contains(s))
                                {
                                    TmpmarkMetastate.ReachableStates.Add(s);
                                    tmplist.Add(s.ID);
                                }
                            }
                            foreach (BDD.Transition t in TmpMetastate2.OutgoingTransitions)
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
                                GeneratedMetastatesKey.Add(TmpmarkMetastate.MKey);
                            else
                            {
                                this.MetaStates.Remove(TmpmarkMetastate);
                                foreach (OGTransition o in TmpMetastate1.OGOutgoingTransitions)
                                {
                                    if (o.ToMstate == TmpmarkMetastate)
                                        TmpMetastate1.OGOutgoingTransitions.Remove(o);
                                }
                                foreach (OGTransition o in this.OGTranstions)
                                {
                                    if (o.ToMstate == TmpmarkMetastate)
                                        this.OGTranstions.Remove(o);
                                }

                                if (MetastateStack.Peek() == TmpmarkMetastate)
                                    MetastateStack.Pop();
                                else
                                {
                                    //copy metastatestack to another array and delete that one
                                }
                            }
                        }
                        //StoreMetastateStack.Push(TmpMetastate2);
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
                    //if (label.Negated)  //negated means?
                    //{
                    if (!(OGBA.DeclarationDatabase.TryGetValue(labelstring, out exp))) //just get event name?
                    {
                        Ename.Add(labelstring);
                    }
                    //else
                    //{
                      //  if() // *****if it is a proposition, how to write a function to judge as in config?**********
                        // ;   
                    //}
                    //}
                }
            }
            foreach (BDD.Transition t in graph.Transitions)
            {
                if (Ename.Contains(t.Event.ToString()))
                {
                    //OBs.Add(t.Event.ToString());
                }
            }

            foreach (string e in synlist)
            {
                if(!(OBs.Contains(e.ToString())))
                {
                    ;
                    //OBs.Add(e);
                }
            }

            //for test
            OBs.Add("obs");
            OBs.Add("sync");
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
            int markcount = 0; //for the final condition
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
                foreach (BDD.Transition t in M[i].OutgoingTransitions)
                {
                    TmpEnable[i] = new List<string>();
                    TmpEnable[i].Add(t.Event.ToString());
                }
            }

            //second condition
            for (i=0;i<2;i++)
            {
                if(ifdead[i] == false)
                {
                    TmpE = synlist.Except(TmpEnable[1-i]);
                    foreach (BDD.State s in M[i].ReachableStates)
                    {
                        foreach (BDD.Transition ss in s.OutgoingTransitions)
                        {
                            TmpSEnable.Add(ss.Event.ToString());
                        }
                        if(TmpSEnable.Intersect(TmpE).Count() != 0)
                        {
                            if(TmpSEnable.Except(TmpE).Count() == 0)
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
                    foreach (BDD.State ss in M[1-i].ReachableStates)
                    {
                        foreach (BDD.Transition t in ss.OutgoingTransitions)
                        {
                            TmpSEnable.Add(t.Event.ToString());
                        }
                        if(TmpSEnable.Intersect(synlist).Count() != 0)
                        {
                            if(TmpSEnable.Except(synlist).Count() == 0)
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
            List<BDD.State> TmpState = new List<BDD.State>();

            Unionlist = TmpEnable[0].Intersect(TmpEnable[1]);
            for (i=0;i<2;i++)
            {
                sync[i] = synlist.Intersect(TmpEnable[i]);

                if(TmpEnable[1-i].Intersect(sync[i]).Count() != 0)
                {
                    if(sync[i].Except(TmpEnable[1-i]).Count() != 0)
                    {
                        TmpUnion = sync[i].Except(TmpEnable[1-i]);
                        sync[i] = sync[i].Except(TmpUnion);
                    }  

                    foreach (BDD.State s in M[1-i].ReachableStates)
                    {
                        foreach (BDD.Transition t in s.OutgoingTransitions)
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
                        foreach (BDD.State ss in TmpState)
                        {
                            foreach(BDD.Transition tt in ss.OutgoingTransitions)
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

        public Dictionary<string, BDD.SymbolicLTS> AllModularLTS; //Basement

        public SynOG()
        {
            SynOGMetastates = new Dictionary<string, SynOGMetastate>();
            //InitialSynOGMetastate = new KeyValuePair<OGMeta_state,OGMeta_state>();
            SynOBTransitions = new List<OGTransition>();
            SynEvents = new List<string>();
            AllModularOGs = new Dictionary<string, ModularOG>();

            AllModularLTS = new Dictionary<string, BDD.SymbolicLTS>();
        }

        public void AddModularOG(ModularOG MOG)
        {
            AllModularOGs.Add(MOG.ID, MOG);
        }

        //BASEMENT
        public void AddModularLTS(BDD.SymbolicLTS MLTS)
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
                foreach (KeyValuePair<string, BDD.SymbolicLTS> mlts in AllModularLTS)
                {
                    MLTSEvents = new List<string>();
                    foreach (BDD.Transition e in mlts.Value.Transitions)
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
                foreach (KeyValuePair<string, BDD.SymbolicLTS> mlts in AllModularLTS)
                    foreach (BDD.Transition e in mlts.Value.Transitions)
                        if (e.Event.BaseName.ToString() == "sync")
                            this.SynEvents.Add(e.ToString());
            }
        }

        public void BuildSynOG(string M1, string M2)
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

                    SynOGMetastates.Add(SOGM.ID, SOGM);
                    SynOBTransitions.Add(SOGT);

                    Todo.Push(SOGM);

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
                        SynOGMetastates.Add(SOGM.ID, SOGM);
                        SynOBTransitions.Add(SOGT);

                        Todo.Push(SOGM);

                        SOGM = new SynOGMetastate();
                        SOGT = new OGTransition();
                    }
                }
            }

            judge = false;
            SynOGMetastate SOGM2 = new SynOGMetastate();
            //following product.
            do
            {
                SOGM = Todo.Pop();
                Mstate1 = SOGM.SynMeta_state.Key;
                Mstate2 = SOGM.SynMeta_state.Value;

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

                        SynOGMetastates.Add(SOGM2.ID, SOGM2);
                        SynOBTransitions.Add(SOGT);

                        Todo.Push(SOGM2);

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

                            SynOGMetastates.Add(SOGM2.ID, SOGM2);
                            SynOBTransitions.Add(SOGT);

                            Todo.Push(SOGM2);

                            SOGM2 = new SynOGMetastate();
                            SOGT = new OGTransition();
                        }
                    }
                }

            } while (Todo.Count > 0);

        }
    }

    public partial class AssertionLTL
    {
        public SynOG SynOBGraph;
        public ModularOG[] ObservationGraph;
        int count;

        public void ModularLTS2SynOG()
        {
            //ObservationGraph = new OG();
            SynOBGraph = new SynOG();
            ObservationGraph = new ModularOG[1];
            count = 0;

            /***ONE LTS AFTER PRODUCT, TO TEST BUILD OG***/
            /*BDD.SymbolicLTS SAMPLE = new BDD.SymbolicLTS();
            Event[] el = new Event[8];
            Event tmp = new Event("a");
            el[0] = tmp;
            tmp = new Event("b");
            el[1] = tmp;
            tmp = new Event("c");
            el[2] = tmp;
            tmp = new Event("d");
            el[3] = tmp;
            tmp = new Event("e");
            el[4] = tmp;
            tmp = new Event("f");
            el[5] = tmp;
            tmp = new Event("sync");
            el[6] = tmp;
            tmp = new Event("obs");
            el[7] = tmp;
            BDD.State[] sl = new BDD.State[11];
            sl[0] = new BDD.State("A1B1", "1");
            sl[1] = new BDD.State("A2B1", "2");
            sl[2] = new BDD.State("A1B2", "3");
            sl[3] = new BDD.State("A3B1", "4");
            sl[4] = new BDD.State("A2B2", "5");
            sl[5] = new BDD.State("A3B2", "6");
            sl[6] = new BDD.State("A4B3", "7");
            sl[7] = new BDD.State("A5B3", "8");
            sl[8] = new BDD.State("A1B3", "9");
            sl[9] = new BDD.State("A2B3", "10");
            sl[10] = new BDD.State("A3B3", "11");
            BDD.Transition[] tl = new BDD.Transition[19];
            
            tl[0] = new BDD.Transition();
            tl[0].Event = el[0];
            tl[0].FromState = sl[0];
            tl[0].ToState = sl[1];
            sl[0].OutgoingTransitions.Add(tl[0]);
            sl[1].IncomingTransition.Add(tl[0]);

            tl[1] = new BDD.Transition();
            tl[1].Event = el[4];
            tl[1].FromState = sl[0];
            tl[1].ToState = sl[2];
            sl[0].OutgoingTransitions.Add(tl[1]);
            sl[2].IncomingTransition.Add(tl[1]);

            tl[2] = new BDD.Transition();
            tl[2].Event = el[5];
            tl[2].FromState = sl[2];
            tl[2].ToState = sl[0];
            sl[2].OutgoingTransitions.Add(tl[2]);
            sl[0].IncomingTransition.Add(tl[2]);

            tl[3] = new BDD.Transition();
            tl[3].Event = el[1];
            tl[3].FromState = sl[0];
            tl[3].ToState = sl[3];
            sl[0].OutgoingTransitions.Add(tl[3]);
            sl[3].IncomingTransition.Add(tl[3]);

            tl[4] = new BDD.Transition();
            tl[4].Event = el[2];
            tl[4].FromState = sl[3];
            tl[4].ToState = sl[3];
            sl[3].OutgoingTransitions.Add(tl[4]);
            sl[3].IncomingTransition.Add(tl[4]);

            tl[5] = new BDD.Transition();
            tl[5].Event = el[4];
            tl[5].FromState = sl[1];
            tl[5].ToState = sl[4];
            sl[1].OutgoingTransitions.Add(tl[5]);
            sl[4].IncomingTransition.Add(tl[5]);

            tl[6] = new BDD.Transition();
            tl[6].Event = el[5];
            tl[6].FromState = sl[4];
            tl[6].ToState = sl[1];
            sl[4].OutgoingTransitions.Add(tl[6]);
            sl[1].IncomingTransition.Add(tl[6]);

            tl[7] = new BDD.Transition();
            tl[7].Event = el[0];
            tl[7].FromState = sl[2];
            tl[7].ToState = sl[4];
            sl[2].OutgoingTransitions.Add(tl[7]);
            sl[4].IncomingTransition.Add(tl[7]);

            tl[8] = new BDD.Transition();
            tl[8].Event = el[1];
            tl[8].FromState = sl[2];
            tl[8].ToState = sl[5];
            sl[2].OutgoingTransitions.Add(tl[8]);
            sl[5].IncomingTransition.Add(tl[8]);

            tl[9] = new BDD.Transition();
            tl[9].Event = el[4];
            tl[9].FromState = sl[3];
            tl[9].ToState = sl[5];
            sl[3].OutgoingTransitions.Add(tl[9]);
            sl[5].IncomingTransition.Add(tl[9]);

            tl[10] = new BDD.Transition();
            tl[10].Event = el[5];
            tl[10].FromState = sl[5];
            tl[10].ToState = sl[3];
            sl[5].OutgoingTransitions.Add(tl[10]);
            sl[3].IncomingTransition.Add(tl[10]);

            tl[11] = new BDD.Transition();
            tl[11].Event = el[2];
            tl[11].FromState = sl[5];
            tl[11].ToState = sl[5];
            sl[5].OutgoingTransitions.Add(tl[11]);
            sl[5].IncomingTransition.Add(tl[11]);

            tl[12] = new BDD.Transition();
            tl[12].Event = el[6];
            tl[12].FromState = sl[4];
            tl[12].ToState = sl[6];
            sl[4].OutgoingTransitions.Add(tl[12]);
            sl[6].IncomingTransition.Add(tl[12]);

            tl[13] = new BDD.Transition();
            tl[13].Event = el[6];
            tl[13].FromState = sl[5];
            tl[13].ToState = sl[7];
            sl[5].OutgoingTransitions.Add(tl[13]);
            sl[7].IncomingTransition.Add(tl[13]);

            tl[14] = new BDD.Transition();
            tl[14].Event = el[7];
            tl[14].FromState = sl[7];
            tl[14].ToState = sl[6];
            sl[7].OutgoingTransitions.Add(tl[14]);
            sl[6].IncomingTransition.Add(tl[14]);

            tl[15] = new BDD.Transition();
            tl[15].Event = el[3];
            tl[15].FromState = sl[6];
            tl[15].ToState = sl[8];
            sl[6].OutgoingTransitions.Add(tl[15]);
            sl[8].IncomingTransition.Add(tl[15]);

            tl[16] = new BDD.Transition();
            tl[16].Event = el[0];
            tl[16].FromState = sl[8];
            tl[16].ToState = sl[9];
            sl[8].OutgoingTransitions.Add(tl[16]);
            sl[9].IncomingTransition.Add(tl[16]);

            tl[17] = new BDD.Transition();
            tl[17].Event = el[1];
            tl[17].FromState = sl[8];
            tl[17].ToState = sl[10];
            sl[8].OutgoingTransitions.Add(tl[17]);
            sl[10].IncomingTransition.Add(tl[17]);

            tl[18] = new BDD.Transition();
            tl[18].Event = el[2];
            tl[18].FromState = sl[10];
            tl[18].ToState = sl[10];
            sl[10].OutgoingTransitions.Add(tl[18]);
            sl[10].IncomingTransition.Add(tl[18]);

            SAMPLE.InitialState = sl[0];
            SAMPLE.Name = "SAMPLE";
            for (int j = 0; j < 11; j++)
                SAMPLE.States.Add(sl[j]);

            for (int j = 0; j < 19; j++)
                SAMPLE.Transitions.Add(tl[j]);*/
            /******************************************/

            /*****LTS TWO, TWO MOULAR LTS FOR TESTING***/
            BDD.SymbolicLTS[] Samplelist = new BDD.SymbolicLTS[2];
            Samplelist[0] = new BDD.SymbolicLTS();
            Samplelist[1] = new BDD.SymbolicLTS();
            Event[] el = new Event[8];
            Event tmp = new Event("a");
            el[0] = tmp;
            tmp = new Event("b");
            el[1] = tmp;
            tmp = new Event("c");
            el[2] = tmp;
            tmp = new Event("d");
            el[3] = tmp;
            tmp = new Event("e");
            el[4] = tmp;
            tmp = new Event("f");
            el[5] = tmp;
            tmp = new Event("sync");
            el[6] = tmp;
            tmp = new Event("obs");
            el[7] = tmp;

            BDD.State[] sl1 = new BDD.State[5];
            sl1[0] = new BDD.State("A1", "1");
            sl1[1] = new BDD.State("A2", "2");
            sl1[2] = new BDD.State("A3", "3");
            sl1[3] = new BDD.State("A4", "4");
            sl1[4] = new BDD.State("A5", "5");

            BDD.State[] sl2 = new BDD.State[3];
            sl2[0] = new BDD.State("B1", "1");
            sl2[1] = new BDD.State("B2", "2");
            sl2[2] = new BDD.State("B3", "3");

            BDD.Transition [] tl1 = new BDD.Transition[7];
            tl1[0] = new BDD.Transition();
            tl1[0].Event = el[0];
            tl1[0].FromState = sl1[0];
            tl1[0].ToState = sl1[1];
            sl1[0].OutgoingTransitions.Add(tl1[0]);
            sl1[1].IncomingTransition.Add(tl1[0]);

            tl1[1] = new BDD.Transition();
            tl1[1].Event = el[1];
            tl1[1].FromState = sl1[0];
            tl1[1].ToState = sl1[2];
            sl1[0].OutgoingTransitions.Add(tl1[1]);
            sl1[2].IncomingTransition.Add(tl1[1]);

            tl1[2] = new BDD.Transition();
            tl1[2].Event = el[2];
            tl1[2].FromState = sl1[2];
            tl1[2].ToState = sl1[2];
            sl1[2].OutgoingTransitions.Add(tl1[2]);
            sl1[2].IncomingTransition.Add(tl1[2]);

            tl1[3] = new BDD.Transition();
            tl1[3].Event = el[6];
            tl1[3].FromState = sl1[1];
            tl1[3].ToState = sl1[3];
            sl1[1].OutgoingTransitions.Add(tl1[3]);
            sl1[3].IncomingTransition.Add(tl1[3]);

            tl1[4] = new BDD.Transition();
            tl1[4].Event = el[3];
            tl1[4].FromState = sl1[3];
            tl1[4].ToState = sl1[0];
            sl1[3].OutgoingTransitions.Add(tl1[4]);
            sl1[3].IncomingTransition.Add(tl1[4]);

            tl1[5] = new BDD.Transition();
            tl1[5].Event = el[6];
            tl1[5].FromState = sl1[2];
            tl1[5].ToState = sl1[4];
            sl1[2].OutgoingTransitions.Add(tl1[5]);
            sl1[4].IncomingTransition.Add(tl1[5]);

            tl1[6] = new BDD.Transition();
            tl1[6].Event = el[7];
            tl1[6].FromState = sl1[4];
            tl1[6].ToState = sl1[3];
            sl1[4].OutgoingTransitions.Add(tl1[6]);
            sl1[3].IncomingTransition.Add(tl1[6]);

            Samplelist[0].InitialState = sl1[0];
            Samplelist[0].Name = "SAMPLE1";
            for (int j = 0; j < 5; j++)
                Samplelist[0].States.Add(sl1[j]);

            for (int j = 0; j < 7; j++)
                Samplelist[0].Transitions.Add(tl1[j]);


            BDD.Transition [] tl2 = new BDD.Transition[3];
            tl2[0] = new BDD.Transition();
            tl2[0].Event = el[4];
            tl2[0].FromState = sl2[0];
            tl2[0].ToState = sl2[1];
            sl2[0].OutgoingTransitions.Add(tl2[0]);
            sl2[1].IncomingTransition.Add(tl2[0]);

            tl2[1] = new BDD.Transition();
            tl2[1].Event = el[5];
            tl2[1].FromState = sl2[1];
            tl2[1].ToState = sl2[0];
            sl2[1].OutgoingTransitions.Add(tl2[1]);
            sl2[0].IncomingTransition.Add(tl2[1]);

            tl2[2] = new BDD.Transition();
            tl2[2].Event = el[6];
            tl2[2].FromState = sl2[1];
            tl2[2].ToState = sl2[2];
            sl2[1].OutgoingTransitions.Add(tl2[2]);
            sl2[2].IncomingTransition.Add(tl2[2]);

            Samplelist[1].InitialState = sl2[0];
            Samplelist[1].Name = "SAMPLE2";
            for (int j = 0; j < 3; j++)
                Samplelist[1].States.Add(sl2[j]);

            for (int j = 0; j < 3; j++)
                Samplelist[1].Transitions.Add(tl2[j]);
            /*******************************************/


            //ADD MODULAR LTS.
            SynOBGraph.AddModularLTS(Samplelist[0]);
            SynOBGraph.AddModularLTS(Samplelist[1]);
            SynOBGraph.GenerateSynEvent();
  
            /***FOR TESTING,MAUNAL GENERATE LTS***/

           

            while (SynOBGraph.AllModularLTS.Count > count)
            {
                ObservationGraph[count] = new ModularOG(ref Samplelist[count]);  //must get graph from pat
                ObservationGraph[count].GenerateObsSet(BA, SynOBGraph.SynEvents);
                ObservationGraph[count].InitMetastate();
                ObservationGraph[count].BuildOG();
                SynOBGraph.AddModularOG(ObservationGraph[count]);
                count++;
            }

            //basement, suppose two modulars
            SynOBGraph.BuildSynOG(ObservationGraph[0].ID, ObservationGraph[1].ID);



        }

        private void OGVerification()   //on-the-fly OG verfication based on tarjan verfication in LTS
        {
        /*   VerificationOutput.CounterExampleTrace = null;


            //out-going table.           
            Dictionary<string, List<string>> OutgoingTransitionTable = new Dictionary<string, List<string>>(Ultility.Ultility.MC_INITIAL_SIZE);

            //DFS Stack
            //Stack<KeyValuePair<ConfigurationBase, string>> TaskStack = new Stack<KeyValuePair<ConfigurationBase, string>>(5000);
            Stack<KeyValuePair<OGMeta_state, string>> TaskStack = new Stack<KeyValuePair<OGMeta_state, string>>(5000); //new

            //DFS data, which mapping each state to an int[] of size 2, first is the pre-order, second is the lowlink
            StringDictionary<int[]> DFSData = new StringDictionary<int[]>(Ultility.Ultility.MC_INITIAL_SIZE);

            //List<KeyValuePair<ConfigurationBase, string>> initials = new List<KeyValuePair<ConfigurationBase, string>>();
            List<KeyValuePair<OGMeta_state, string>> initials = new List<KeyValuePair<OGMeta_state, string>>();

            HashSet<string> existed = new HashSet<string>();

            foreach (string s in BA.InitialStates)
            {
                //List<string> next = BA.MakeOneMove(s, InitialStep);
                //List<string> next = BA.MakeOneMove(s, ObservationGraph.InitialMetaState); 

                //Problem:For Proposition, what should I do?

                foreach (string var in next)
                {
                    //if (!existed.Contains(var))
                    //{
                    //    existed.Add(var);
                    //    initials.Add(new KeyValuePair<ConfigurationBase, string>(InitialStep, var));
                    //}
                    if (existed.Add(var))
                    {
                        //initials.Add(new KeyValuePair<ConfigurationBase, string>(InitialStep, var));
                        initials.Add(new KeyValuePair<OGMeta_state, string>(ObservationGraph.InitialMetaState, var));
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
                //KeyValuePair<ConfigurationBase, string> initState = initials[z];
                KeyValuePair<OGMeta_state, string> initState = initials[z];   //new
                TaskStack.Push(initState);
                //string ID = initState.Key.GetIDWithEvent() + Constants.SEPARATOR + initState.Value;  //new
                string ID = initState.Key.ID + Constants.SEPARATOR + initState.Value;

                DFSData.Add(ID, new int[] { VISITED_NOPREORDER, 0 });
                OutgoingTransitionTable.Add(ID, new List<string>(8));
            }

            List<string> StronglyConnectedComponets = new List<string>(1024);
            //Stack<KeyValuePair<ConfigurationBase, string>> stepStack = new Stack<KeyValuePair<ConfigurationBase, string>>(1024);
            Stack<KeyValuePair<OGMeta_state, string>> stepStack = new Stack<KeyValuePair<OGMeta_state, string>>(1024); //new

            //# Preorder counter 
            int i = 0;

            //store the expended event step of a node to avoid multiple invocation of the make one move.
            //Dictionary<string, List<KeyValuePair<ConfigurationBase, string>>> ExpendedNode = new Dictionary<string, List<KeyValuePair<ConfigurationBase, string>>>(1024);
            Dictionary<string, List<KeyValuePair<OGMeta_state, string>>> ExpendedNode = new Dictionary<string, List<KeyValuePair<OGMeta_state, string>>>(1024);

            do
            {
                if (CancelRequested)
                {
                    VerificationOutput.NoOfStates = DFSData.Count; // VisitedWithID.Count;
                    return;
                }

                //KeyValuePair<ConfigurationBase, string> pair = TaskStack.Peek();
                //ConfigurationBase config = pair.Key;
                KeyValuePair<OGMeta_state, string> pair = TaskStack.Peek(); //new
                OGMeta_state ms = pair.Key;

                //string v = pair.Key.GetIDWithEvent() + Constants.SEPARATOR + pair.Value;
                string v = pair.Key.ID + Constants.SEPARATOR + pair.Value;

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
                    //List<KeyValuePair<ConfigurationBase, string>> list = ExpendedNode[v];
                    List<KeyValuePair<OGMeta_state, string>> list = ExpendedNode[v];
                    if (list.Count > 0)
                    {
                        //transverse all steps
                        for (int k = list.Count - 1; k >= 0; k--)
                        {
                            //KeyValuePair<ConfigurationBase, string> step = list[k];
                            KeyValuePair<OGMeta_state, string> step = list[k]; //new

                            //if the step is a unvisited step
                            //string tmp = step.Key.GetIDWithEvent() + Constants.SEPARATOR + step.Value;
                            string tmp = step.Key.ID + Constants.SEPARATOR + step.Value; //new

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
                    //IEnumerable<ConfigurationBase> list = config.MakeOneMove(); //which makeonemove?
                    IEnumerable<OGMeta_state> list = ms.MakeOneMove();

                    //List<KeyValuePair<ConfigurationBase, string>> product = new List<KeyValuePair<ConfigurationBase, string>>();
                    List<KeyValuePair<OGMeta_state, string>> product = new List<KeyValuePair<OGMeta_state, string>>(); //new

                    foreach (OGMeta_state step in list)
                    {
                        //List<string> states = BA.MakeOneMove(pair.Value, step);
                        List<string> states = BA.MakeOneMove(pair.Value, step);

                        for (int j = 0; j < states.Count; j++)
                        {
                            //product.Add(new KeyValuePair<ConfigurationBase, string>(step, states[j]));
                            product.Add(new KeyValuePair<OGMeta_state, string>(step, states[j]));
                        }
                    }

                    //count the transitions visited
                    VerificationOutput.Transitions += product.Count;

                    for (int k = product.Count - 1; k >= 0; k--)
                    {
                        //KeyValuePair<ConfigurationBase, string> step = product[k];
                        //string tmp = step.Key.GetIDWithEvent() + Constants.SEPARATOR + step.Value;
                        KeyValuePair<OGMeta_state, string> step = product[k];
                        string tmp = step.Key.ID + Constants.SEPARATOR + step.Value;

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
                            //KeyValuePair<ConfigurationBase, string> valuePair = stepStack.Peek();
                            //string k = valuePair.Key.GetIDWithEvent() + Constants.SEPARATOR + valuePair.Value;
                            KeyValuePair<OGMeta_state, string> valuePair = stepStack.Peek();
                            string k = valuePair.Key.ID + Constants.SEPARATOR + valuePair.Value;

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
                                    //k = valuePair.Key.GetIDWithEvent() + Constants.SEPARATOR + valuePair.Value;
                                    k = valuePair.Key.ID + Constants.SEPARATOR + valuePair.Value; //new
                                }
                            }
                        }

                        if (BuchiFair && (ms.IfDead || StronglyConnectedComponets.Count > 1 || selfLoop))   //new
                        {
                            VerificationOutput.VerificationResult = VerificationResultType.INVALID;
                            VerificationOutput.NoOfStates = DFSData.Count;

                            while (TaskStack.Count > 0 && TaskStack.Peek().Key.Event != Constants.INITIAL_EVENT) //???
                            {
                                TaskStack.Pop();
                            }

                            string startID = null;
                            if (TaskStack.Count > 0)
                            {
                                startID = TaskStack.Peek().Key.GetIDWithEvent() + Constants.SEPARATOR +
                                            TaskStack.Peek().Value;    //?
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
            return;*/
        }
    }
    
}