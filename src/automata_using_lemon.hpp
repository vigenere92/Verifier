/*

Copyright (C) 2013 Gaurav Saini, Subham Modi

This file is part of Verifier.

Verifier is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Verifier is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Verifier. If not, see <http://www.gnu.org/licenses/>.

*/

#include "xml2automata.hpp"

class CommunicatingProcess
{
    std::unordered_map<std::string,bool> Connc_comp_map;
    vector<Process_pointer> Processes ;
    vector<Nname_pointer> Process_state_name;
    vector<Avalues_pointer> Process_transition_message;
    vector<Avalues_pointer> Process_transition_symbol;
    vector<Cvalue_pointer> Process_channel;
    vector<ListDigraph::Node> Process_initial_state;
    vector<ListDigraph::Node > Process_final_state;
    vector<string> Aut_messages;
    vector<string> Process_roles;
    std::unordered_map<std::string ,std::unordered_set<std::string> > Channels;
    
    public:
    
        /** Constructor for the CommunicationProcess class. It takes the path to XML file and the channel_type variable for creating channels as arguments. */
        CommunicatingProcess(string file_path, string channel_type)
        {

            const char* f_path = file_path.c_str();
            Translator translator(f_path);
            Processes = translator.get_Processes();
            Process_state_name = translator.get_Process_state_name();
            Process_transition_message = translator.get_Process_transition_message();
            Process_transition_symbol = translator.get_Process_transition_symbol();
            Process_initial_state = translator.get_Process_initial_state();
            Process_final_state = translator.get_Process_final_state();
            Process_channel = translator.get_Process_channel();
            Aut_messages = translator.get_Aut_messages();
            Process_roles = translator.get_Process_roles();
            cout<<endl<<"; removing send loops"<<endl;
            
            for(int i=0;i<Processes.size();i= i+2)
                remove_send_loops(Processes[i],Process_state_name[i],Process_transition_symbol[i],Process_transition_message[i],Process_initial_state[i],Process_final_state[i],Process_channel[i]);
            if(channel_type == "xml")
                Channels = translator.get_PChannels();
            else
                generate_channels(channel_type);       
        }
        
        ///Fucntion to generate channels when channels are not specified in the XML file.
        void generate_channels(string channel_type)
        {
            if(channel_type == "prefix")
            {
                for(int i=0;i<Aut_messages.size();i++)
                {
                    const char* theval;
                    string sym(1, ((Aut_messages[i])[0]));
                    theval = sym.c_str();
                    Channels[theval].insert((Aut_messages[i]));
                }
            }    
            else if( channel_type == "process")
            {
                for(int i=0,j=0;i<Processes.size();i=i+2,j=j+1)
                {
                    string prole = Process_roles[j];
                    for(ListDigraph::ArcIt ai(*(Processes[i])); ai != INVALID; ++ai)
                    {
                        string msg = (*(Process_transition_symbol[i]))[ai];
                        Channels[prole].insert(msg);
                    }
                }
            }
        }
            
        ///Function to check whether a state is unique or not.
        bool check_unique_state(string state)
        {
            if(state.find("I_$$") == 0 || state.find("F_$$") == 0)
                return true;
            else
                return false;
        }

        ///Function to check whether a state is left unique.
        bool check_left_unique_state(string state)
        {
            if(state.find("I_$$") == 0)
                return true;
            else
                return false;
        }

        ///Function to check whether a state is right unique.
        bool check_right_unique_state(string state)
        {
            if(state.find("F_$$") == 0)
                return true;
            else
               return false;
        }
         
        ///Function to check whether a transition is one of the unique transitions.
        bool check_unique(ListDigraph::Arc trans, Process_pointer process,Nname_pointer state_name)
        {
            string source, target;
            source = (*state_name)[process->source(trans)];
            target = (*state_name)[process->target(trans)];
            if(source.find("I_$$") == 0 && target.find("F_$$") == 0)
                return true;
            else
                return false;
        }
        
        ///Function to check whether a transition is left unique.
        bool check_left_unique(ListDigraph::Arc trans, Process_pointer process,Nname_pointer state_name)
        {
            string source;
            source = (*state_name)[process->source(trans)];
            if(source.find("I_$$") == 0)
                return true;
            else
                return false;
        }
        
        ///Function to check whether a transition is right unique.
        bool check_right_unique(ListDigraph::Arc trans, Process_pointer process,Nname_pointer state_name)
        {
            string target;
            target = (*state_name)[process->target(trans)];
            if(target.find("F_$$") == 0)
                return true;
            else
                return false;
        }
        
        ///Function to get the transitions coming into a state.
        vector<ListDigraph::Arc>  get_state_in_transition(ListDigraph::Node state, Process_pointer process)
        {
            vector<ListDigraph::Arc> trans_list;
            for(ListDigraph::InArcIt inE(*process, state); inE != INVALID ; ++inE)
                trans_list.push_back(inE);

            return trans_list;
        }
        
        ///Function to get the transitions coming out of a state.
        vector<ListDigraph::Arc>  get_state_out_transition(ListDigraph::Node state, Process_pointer process)
        {
            vector<ListDigraph::Arc> trans_list;
            for(ListDigraph::OutArcIt inE(*process, state); inE != INVALID ; ++inE)
                trans_list.push_back(inE);

            return trans_list;
        }
        
        ///Function to find the number of unique transitions.
        int get_unique_no()
        {
            int u_trans = 0;
            for(int i=0;i<Processes.size();i++)
                for(ListDigraph::ArcIt a(*(Processes[i])); a != INVALID; ++a)
                    if(check_unique(a,Processes[i],Process_state_name[i]))
                        u_trans++;

            return u_trans;
                
        }

        int min(int a, int b)
        {
            if(a > b)
                return b;
            else
                return a;
        }
        
        ///Function to check whether a given node is present in the stack.
        bool present_in_stack(ListDigraph::Node a,std::stack<ListDigraph::Node> state_stack)
        {
            std::stack<ListDigraph::Node> stack1 = state_stack;
            for(int k =0 ; k< state_stack.size();k++)
            {
                if(a == stack1.top())
                    return true;
                else
                    stack1.pop();
            }

            return false;
        }
                
        ///Function to generate the strongly connected components of the graph.
        void strong_connect(ListDigraph::Node a,Process_pointer process, Nname_pointer state_name,ListDigraph::NodeMap<bool> &State_visited,ListDigraph::NodeMap<int> &State_sequence,ListDigraph::NodeMap<int> &State_nearest, std::stack<ListDigraph::Node> &state_stack,int &i)
        {
            State_sequence[a] = i;
            State_visited[a] = true;
            State_nearest[a] = i;
            ++i;
            state_stack.push(a);
            for(ListDigraph::OutArcIt oute(*process,a);oute!=INVALID;++oute)
            {
                ListDigraph::Node te1 = process->target(oute);
                if(State_visited[process->target(oute)] == false)
                {
                    strong_connect((process->target(oute)),process,state_name,State_visited,State_sequence,State_nearest,state_stack,i);
                    State_nearest[a] = min(State_nearest[a],State_nearest[process->target(oute)]);
                }
                else if ( present_in_stack(process->target(oute), state_stack))
                {
                    State_nearest[a] = min(State_nearest[a],State_sequence[process->target(oute)]);
                }
            }
            
            if(State_sequence[a] == State_nearest[a])
            {
                ListDigraph::Node b = state_stack.top();
                state_stack.pop();
                while((*state_name)[b] != (*state_name)[a])
                {
                    b = state_stack.top();
                    state_stack.pop();
                }
            }
        }
            
        ///Function to remove the send loops from the graph.
        void remove_send_loops(Process_pointer process,Nname_pointer state_name, Avalues_pointer transition_symbol,Avalues_pointer transition_message,ListDigraph::Node &initial_state,ListDigraph::Node P_final_state,Cvalue_pointer pchannel)
        {
            ListDigraph::NodeMap<bool> State_visited(*process);
            ListDigraph::NodeMap<int> State_sequence(*process);
            ListDigraph::NodeMap<int> State_nearest(*process);
            ListDigraph::NodeMap<int> State_iteration(*process);
            ListDigraph::Node adjacent_node;
            std::stack<ListDigraph::Node> state_stack;
            vector< vector <ListDigraph::Node> > strong_vertices(countNodes(*process)+1);
            int k=0;
            for(ListDigraph::NodeIt a(*process); a!= INVALID ;++a)
            State_visited[a] = false;
            int i=0;
            for(ListDigraph::NodeIt a(*process); a!= INVALID;++a)
            {
                if(State_visited[a] == false)
                    strong_connect(a,process,state_name,State_visited,State_sequence,State_nearest,state_stack,i);
            }
                
            for(ListDigraph::NodeIt a(*process); a!= INVALID;++a)
                (strong_vertices[State_nearest[a]]).push_back(a);

            for(int i=0;i<strong_vertices.size();i++)
            {
                if(strong_vertices[i].size() == 1)
                {
                    
                    ListDigraph::Node node = (strong_vertices[i])[0];
                    ListDigraph::OutArcIt outE(*process,node);
                    ListDigraph::Arc tem1;
                    bool tag = false, tag1 = false;
                    while(outE != INVALID)
                    {
                        ListDigraph::Node s1,s2;
                        if(process->source(outE) == process->target(outE))
                        {
                            tag1 = true;
                            if(tag == true)
                            {
                                string ms2 = (*transition_symbol)[outE];
                                string ch2 = (*pchannel)[outE];
                                ch2 = (*pchannel)[tem1] + "$$" + ch2;
                                (*pchannel)[tem1] = ch2;
                                ms2 = (*transition_symbol)[tem1] + "$$" + ms2;
                                (*transition_symbol)[tem1] = ms2;
                            }
                            
                            if(tag == false)
                            {
                                string temp = (*state_name)[(strong_vertices[i])[0]];
                                temp = temp.substr(0,temp.length()-2);
                                temp = temp + "_R";
                                Connc_comp_map[temp] = true;
                                s1 = process->addNode();
                                s2 = process->addNode();
                                string state =(*state_name)[node],state1;
                                state1 = "F_$$" + state;
                                state = "I_$$" + state;
                                string message = "";

                                for(ListDigraph::OutArcIt outE1(*process,node);outE1 != INVALID ; ++outE1)
                                {
                                    if(process->source(outE1) == process->target(outE1))
                                    {}
                                    else
                                    {
                                        ListDigraph::Arc trans = process->addArc(s2,process->target(outE1));
                                        (*transition_symbol)[trans] = (*transition_symbol)[outE1];
                                        (*transition_message)[trans] = (*transition_message)[outE1];
                                        (*pchannel)[trans] = (*pchannel)[outE1];
                                    }
                                }

                                for(ListDigraph::InArcIt inE1(*process,node);inE1 != INVALID ; ++inE1)
                                {
                                    if(process->source(inE1) == process->target(inE1))
                                    {}
                                    else
                                    {
                                        ListDigraph::Arc trans = process->addArc(process->source(inE1),s1);
                                        (*transition_symbol)[trans] = (*transition_symbol)[inE1];
                                        (*transition_message)[trans] = (*transition_message)[inE1];
                                        (*pchannel)[trans] = (*pchannel)[inE1];
                                    }
                                }
                                
                                ListDigraph::Arc trans = process->addArc(s1,s2);
                                (*state_name)[s1] = state;
                                (*state_name)[s2] = state1;
                                tem1 =  trans;
                                (*transition_message)[trans] = (*transition_message)[outE];
                                (*transition_symbol)[trans] = (*transition_symbol)[outE];
                                (*pchannel)[trans] = (*pchannel)[outE];
                                tag = true;
                            }
                        }

                        ++outE;
                        if(outE == INVALID && tag1 == true)
                        {
                            if((*state_name)[initial_state] == (*state_name)[node])
                                initial_state = s1;
                            process->erase(node);
                        }
                        
                    }                    
                }
                else if((strong_vertices[i]).size() > 1)
                {
                    ListDigraph::Node s1 = process->addNode();
                    ListDigraph::Node s2 = process->addNode();
                    string state ="";
                    string message = "";
                    string tchannel = "";
                    for(int j=0;j< (strong_vertices[i]).size();j++)
                    {
                        string temp = (*state_name)[(strong_vertices[i])[j]];
                        int s = temp.find("_S");
                        temp.replace(s,(temp.size() - 1), "_R");
                        Connc_comp_map[temp] = true;
                        state.append((*state_name)[(strong_vertices[i])[j]]);

                        if(j != (strong_vertices[i].size() - 1))
                            state = state + "$$";
                        ListDigraph::OutArcIt outE(*process,(strong_vertices[i])[j]);

                        while(outE != INVALID) 
                        {
                            l2:
                            int flag = 1;
                            for(int l =0 ; l < (strong_vertices[i]).size(); l++)
                            {
                                if((*state_name)[((strong_vertices[i])[l])] == (*state_name)[process->target(outE)])
                                {
                                        message.append((*transition_symbol)[outE]);
                                        message = message + "$$";
                                        tchannel.append((*pchannel)[outE]);
                                        tchannel = tchannel + "$$";
                                     
                                    flag = 0;
                                    ListDigraph::Arc tempo2 = outE;
                                    ++outE;
                                    process->erase(tempo2);
                                }
                            }
                             
                            if(flag == 1)
                            {
                                for(ListDigraph::OutArcIt oi(*process,s2);oi!=INVALID;++oi)
                                {
                                    ListDigraph::Node n1 = process->target(outE), n2 = process->target(oi);
                                     if((process->target(outE) == process->target(oi)) && ((*transition_symbol)[outE] == (*transition_symbol)[oi]) && ((*transition_message)[outE] == (*transition_message)[oi]))
                                    {
                                        ListDigraph::Arc tem2 = outE;
                                        ++outE;
                                        process->erase(tem2);
                                        goto l2;
                                    }
                                }
                                 
                                ListDigraph::Arc trans1 = process->addArc(s2,process->target(outE));
                                (*transition_symbol)[trans1] = (*transition_symbol)[outE];
                                (*transition_message)[trans1] = (*transition_message)[outE];
                                (*pchannel)[trans1] = (*pchannel)[outE];
                                ListDigraph::Arc tempo2 = outE;
                                ++outE;
                                process->erase(tempo2);
                                continue;
                            }
                                 
                        }

                            ListDigraph::InArcIt inE(*process,(strong_vertices[i])[j]);
                            while(inE != INVALID)
                            {
                                l3:
                                int flag = 1;
                                for(int l =0 ; l < (strong_vertices[i]).size(); l++)
                                    if(((*state_name)[((strong_vertices[i])[l])] == (*state_name)[process->source(inE)]))
                                         flag = 0;

                                if(flag == 1)
                                {
                                    for(ListDigraph::InArcIt oi(*process,s1);oi!=INVALID;++oi)
                                    {
                                        ListDigraph::Node n1 = process->source(inE), n2 = process->source(oi);
                                        if((process->source(inE) == process->source(oi)) && ((*transition_symbol)[inE] == (*transition_symbol)[oi]) && ((*transition_message)[inE] == (*transition_message)[oi]))
                                        {
                                            ListDigraph::Arc tem2 = inE;
                                            ++inE;
                                            process->erase(tem2);
                                            goto l3;
                                        }
                                    }

                                    ListDigraph::Arc trans1 = process->addArc(process->source(inE),s1);
                                    (*transition_symbol)[trans1] = (*transition_symbol)[inE];
                                    (*transition_message)[trans1] = (*transition_message)[inE];
                                    (*pchannel)[trans1] = (*pchannel)[inE];
                                    ListDigraph::Arc tem2 = inE;
                                    ++inE;
                                    process->erase(tem2);
                                    continue;
                                }
                                ++inE;
                            }
                        }
                    string state1;
                    state1 = state;
                    state = "I_$$"+state;
                    state1 = "F_$$"+state1;
                    (*state_name)[s1] = state;
                    (*state_name)[s2] = state1;
                    ListDigraph::Arc tem = process->addArc(s1,s2);
                    (*transition_message)[tem] = "send";
                    (*transition_symbol)[tem] = message;
                    (*pchannel)[tem] = tchannel;

                    for(int j=0;j < (strong_vertices[i]).size();j++)
                    {
                        ListDigraph::Node strong = ((strong_vertices[i])[j]);
                        if((*state_name)[strong] == (*state_name)[initial_state])
                            initial_state = s1;
                        process->erase(strong);
                    }
                }
                 
            }
        }
        
        
        ///Function to return the transitions of the given process.
        vector<ListDigraph::Arc> get_transitions(Process_pointer process)
        {
            vector<ListDigraph::Arc> transition_list;
            for(ListDigraph::ArcIt edge_iterator(*process); edge_iterator != INVALID ; ++edge_iterator)
                transition_list.push_back(edge_iterator);

            return transition_list;
        }
         
        ///Function to return the states of the given process. 
        vector<string> get_states(Process_pointer process,Nname_pointer state_name)
        {
            vector<string> state_list;
            for(ListDigraph::NodeIt ni(*process) ; ni != INVALID ; ++ni)
                state_list.push_back((*state_name)[ni]);

            return state_list;            
        }

        vector<Process_pointer> get_Processes()
        {
            return Processes;
        }
        
        vector<Nname_pointer> get_Process_state_name()
        {
            return Process_state_name;
        }

        vector<Avalues_pointer> get_Process_transition_message()
        {
            return Process_transition_message;
        }

        vector<Avalues_pointer> get_Process_transition_symbol()
        {
            return Process_transition_symbol;
        }

        vector<ListDigraph::Node> get_Process_initial_state()
        {
            return Process_initial_state;
        }

        vector<ListDigraph::Node>  get_Process_final_state()
        {
            return Process_final_state;
        }
        
        vector<string> get_Aut_messages()
        {
            return Aut_messages;
        }
        
        vector<string> get_Process_roles()
        {
            return Process_roles;
        }
        
        std::unordered_map<std::string ,std::unordered_set<std::string> > get_Channels()
        {
            return Channels;
        }
            
        std::unordered_map<std::string,bool> get_Connc_comp_map()
        {
            return Connc_comp_map;
        }     
        
        vector<Cvalue_pointer> get_PChannels()
        {
            return Process_channel;
        }        
};