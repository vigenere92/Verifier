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

#include "main_header.hpp"

class Translator
{
    ///Process_channel is a vector, where the ith object of the vector maps transitions of the ith process to the corresponding channel.
    vector<Cvalue_pointer> Process_channel;
    ///Processes is a vector, where each object refers to the graph of either the send phase or receive phase of a process.
    vector<Process_pointer> Processes;
    ///Process_state_name is a vector, where ith object maps the state of the ith process to the correspoing state name.
    vector<Nname_pointer> Process_state_name;
    /**Process_transition_message is a vector, where ith object maps the the transition of ith process to corresponding message, which is 
     * send,receive or eps.*/
    vector<Avalues_pointer> Process_transition_message;
    ///Process_transition_symbol is a vector, where ith object maps the transition of ith process to corresponding symbol on the transition.
    vector<Avalues_pointer> Process_transition_symbol;
    ///Process_initial_state is a vector, where ith object corresponds to the initial state of ith process.
    vector<ListDigraph::Node> Process_initial_state;
    ///Process_final_state is a vector, where ith object corresponds to the final state of the ith process.
    vector<ListDigraph::Node> Process_final_state;
    ///Aut_messages is a vector containing all the messages used in the protocol.
    vector<string> Aut_messages;
    ///Process_roles is a vector containing the names of all the processes.
    vector<string> Process_roles;
    ///Channels is a map, where each channel is mapped to the correspoing set of messages.
    std::unordered_map<std::string ,std::unordered_set<std::string> > Channels;

    public:
        Translator(const char* path)
        {
            generate_automata(path);
        }
         
        /** Variable containing the path to XML file is passed to the function. In this function the XML file is parsed, states and 
         *  transitions are added while creating separate copies for send phase and receive phase */  
        void generate_automata(const char* path)
        {
            cout << "; loading xml file" << endl;
            string bad_role = "RECEIVER";
            xml_document xml;
            xml_parse_result xml_result = xml.load_file(path);
            if(!strcmp(xml_result.description(),"File was not found"))
            {
                cout << "Xml File not found!" << endl << "Exiting" << endl;
                exit(0);
            }

            xml_node temp = xml.first_child();
            typedef ListDigraph::Node state;
            typedef ListDigraph::Arc  transition;

            for(xml_node tem1 = temp.child("messages").child("message");tem1;tem1 = tem1.next_sibling())
                Aut_messages.push_back(tem1.child_value());
                
                
            for(temp = temp.child("role");temp;temp = temp.next_sibling("role"))
            {
                ///Adding states to the Graph
                string role = temp.attribute("name").value();
                cout<<endl<<"; adding states for process "<<role;
                Process_roles.push_back(role);
                Process_pointer process(new Graph);
                Process_pointer process1(new Graph);
                std:shared_ptr<Node_namess> state_name = std::make_shared<Node_namess>(*process);
                shared_ptr<Node_namess> state_name1 = std::make_shared<Node_namess>(*process1);
                Avalues_pointer transition_message = std::make_shared<Arc_valuess>(*process);
                Avalues_pointer transition_symbol = std::make_shared<Arc_valuess>(*process);
                Avalues_pointer transition_message1 = std::make_shared<Arc_valuess>(*process1);
                Avalues_pointer transition_symbol1 = std::make_shared<Arc_valuess>(*process1);
                Cvalue_pointer Pchannel = std::make_shared<Channel_valuess>(*process);
                Cvalue_pointer Pchannel1 = std::make_shared<Channel_valuess>(*process1);
                state initial_state,initial_state1,vertex,vertex1,vertex2,vertex3,from_vertex,to_vertex,from_vertex1,to_vertex1;
                transition edge,edge1;
                vector<state> final_state,final_state1;
                vertex2 = process->addNode();
                
                string fstate;
                fstate = role+"_FINAL_STATE_S";
                
                (*state_name)[vertex2] = fstate;
                string fstate1;
                fstate1 = role+"_FINAL_STATE_R"; 
                vertex3 = process1->addNode();
                (*state_name1)[vertex3] = fstate1;
                
                for(xml_node temp1 = temp.child("states").child("state");temp1;temp1 = temp1.next_sibling())
                {
                    string state,state1;
                    state = state1 = temp1.child_value();
                    state = role + "_" + state + "_S";
                    state1 = role + "_" + state1 + "_R";
                    vertex = process->addNode();
                    vertex1 = process1->addNode();
                    (*state_name)[vertex] = state;
                    (*state_name1)[vertex1] = state1;

                    if(temp1.attribute("type") && (!strcmp(temp1.attribute("type").value(),"initial")))
                    {
                        initial_state = vertex;
                        initial_state1 = vertex1;
                    }
                    if(temp1.attribute("type") && (!strcmp(temp1.attribute("type").value(),"final")))
                        ListDigraph::Arc f_edge;
                }
                
                ///Adding transitions to the Graph
                cout<<endl<<"; adding transitions for process "<<role;
                for(xml_node temp2 = temp.child("rule"); temp2 ; temp2 = temp2.next_sibling())
                {
                    string from_state, to_state,from_state1,to_state1, send_symbol, receive_symbol,channel1,channel2;
                    from_state = temp2.child("pre").child("current_state").child_value();
                    from_state1 = from_state;
                    from_state = role+"_"+from_state+"_S";
                    from_state1 = role+"_"+from_state1+"_R";
                    to_state = temp2.child("post").child("next_state").child_value();
                    to_state1 = to_state;
                    to_state = role+"_"+to_state+"_S";
                    to_state1 = role+"_"+to_state1+"_R";

                    for(ListDigraph::NodeIt n(*process); n != INVALID; ++n)
                    {
                        if((*state_name)[n] == (from_state))
                        from_vertex = n;
                        if((*state_name)[n] == (to_state))
                        to_vertex = n;
                    }

                    for(ListDigraph::NodeIt n(*process1); n != INVALID; ++n)
                    {
                        if((*state_name1)[n] == (from_state1))
                            from_vertex1 = n;
                        if((*state_name1)[n] == (to_state1))
                            to_vertex1 = n;
                    }
                    if(temp2.child("pre").child("channel"))
                        channel1 = temp2.child("pre").child("channel").child_value();
                    else
                        channel1 = "";
                    
                    if(temp2.child("post").child("channel"))
                        channel2 = temp2.child("post").child("channel").child_value();
                    else
                        channel2 = "";
                    
                    if(temp2.child("pre").child("received_message"))
                    {
                        receive_symbol = temp2.child("pre").child("received_message").child_value();
                        Channels[channel1].insert(receive_symbol);
                    }
                    else
                        receive_symbol = "";

                    if(temp2.child("post").child("send_message"))
                    {
                        send_symbol = temp2.child("post").child("send_message").child_value();
                        Channels[channel2].insert(send_symbol);
                    }
                    else 
                        send_symbol = "";
                    
                    if(send_symbol == "" && (receive_symbol == "" || receive_symbol == "eps"))
                    {
                        edge = process->addArc(from_vertex,to_vertex);
                        edge1 = process1->addArc(from_vertex1,to_vertex1);
                        (*transition_symbol)[edge] = "eps";
                        (*transition_message)[edge] = "eps";
                        (*transition_symbol1)[edge1] = "eps";
                        (*transition_message1)[edge1] = "eps";
                    }
                    else if(receive_symbol == "")
                    {
                        edge = process->addArc(from_vertex,to_vertex);
                        (*transition_symbol)[edge] = send_symbol;
                        (*Pchannel)[edge] = channel2;
                        (*transition_message)[edge] = "send";
                    }
                    else if(send_symbol == "")
                    {
                        edge1 = process1->addArc(from_vertex1,to_vertex1);
                        (*transition_symbol1)[edge1] = receive_symbol;
                        (*Pchannel1)[edge1] = channel1;
                        (*transition_message1)[edge1] = "receive";
                    }
                    else
                    {
                        string intermediate_state,intermediate_state1;
                        intermediate_state = role +"_INTERMEDIATE_"+ temp2.attribute("id").value() + "_S";
                        intermediate_state1 = role +"_INTERMEDIATE_"+ temp2.attribute("id").value() + "_R";
                        vertex = process->addNode();
                        vertex1 = process1->addNode();
                        (*state_name)[vertex] = intermediate_state;
                        (*state_name1)[vertex1] = intermediate_state1;
                        edge1 = process1->addArc(from_vertex1,vertex1);
                        (*Pchannel1)[edge1] = channel1;
                        (*transition_symbol1)[edge1] = receive_symbol;
                        (*transition_message1)[edge1] = "receive";
                        edge = process->addArc(vertex,to_vertex);
                        (*Pchannel)[edge] = channel2;
                        (*transition_symbol)[edge] = send_symbol;
                        (*transition_message)[edge] = "send";
                    }
                }
                
                Process_initial_state.push_back(initial_state);
                Process_final_state.push_back(vertex2);  
                Processes.emplace_back(process);
                Process_initial_state.push_back(initial_state1);
                Process_final_state.push_back(vertex3);        
                Processes.emplace_back(process1);
                Process_state_name.push_back(state_name);
                Process_transition_symbol.push_back(transition_symbol);
                Process_transition_message.push_back(transition_message);
                Process_state_name.push_back(state_name1);
                Process_transition_symbol.push_back(transition_symbol1);
                Process_transition_message.push_back(transition_message1); 
                Process_channel.push_back(Pchannel);
                Process_channel.push_back(Pchannel1);       
            }
            
        }
        
        ///Function to return the Processes variable.
        vector<Process_pointer> get_Processes()
        {
            return Processes;
        }
        
        ///Function to return the Process_state_name variable.
        vector<Nname_pointer> get_Process_state_name()
        {
            return Process_state_name;
        }
        
        ///Function to return the Process_transition_message variable.
        vector<Avalues_pointer> get_Process_transition_message()
        {
            return Process_transition_message;
        }
        
        ///Function to return the Processe_transition_symbol variable.
        vector<Avalues_pointer> get_Process_transition_symbol()
        {
            return Process_transition_symbol;
        }
        
        ///Function to return the Processe_initial_state variable.
        vector<ListDigraph::Node> get_Process_initial_state()
        {
            return Process_initial_state;
        }
        
        ///Function to return the Processe_final_state variable.
        vector<ListDigraph::Node>  get_Process_final_state()
        {
            return Process_final_state;
        }
        
        ///Function to return the Aut_messages variable.
        vector<string> get_Aut_messages()
        {
            return Aut_messages;
        }
        
        ///Function to return the Process_roles variable.
        vector<string> get_Process_roles()
        {
            return Process_roles;
        }
        
        ///Function to return the Process_channel variable.
        vector<Cvalue_pointer> get_Process_channel()
        {
            return Process_channel;
        }
        
        ///Function to return the Channels variable.
        std::unordered_map<std::string ,std::unordered_set<std::string> > get_PChannels()
        {
            return Channels;
        }      
};