using System.Collections.Generic;
using PAT.Common.Classes.Expressions.ExpressionClass;
namespace PAT.LTS.LTS
{
    public class State
    {
        public List<Transition> OutgoingTransitions;
        public string Name;
        /// <summary>
        /// Integer type
        /// </summary>
        public string ID;

        public State(string name, string id)
        {
            Name = name;
            ID = id;
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
}
