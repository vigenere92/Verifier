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

#include "automata_using_lemon.hpp"

/*Generates automata from xml file and by creating an object of class CommunicatingProcess and then
also generates presburger formula type input to be solved by smt solver*/
class Constraint
{
    //Private member variables of the class Constraint
    int unique;
    int num_asserts;
    string query;
    clock_t c_time;
    std::unordered_map<std::string,bool> Connc_comp_map;
    vector<Process_pointer> Processes ;
    vector<Nname_pointer> Process_state_name;
    vector<Avalues_pointer> Process_transition_message;
    vector<Avalues_pointer> Process_transition_symbol;
    vector<ListDigraph::Node> Process_initial_state;
    vector<ListDigraph::Node > Process_final_state;
    vector<string> Aut_messages;
    vector<string> Process_roles;
    std::unordered_map<std::string ,std::unordered_set<std::string> > Channels;
    std::unordered_map<string,bool> Check;
    std::unordered_map<string, vector<string> > bad;
    vector<Cvalue_pointer> Process_channel;

    //Public member functions of the class Constraint
    public:
        /*Constructor of class Constraint.
        Generates automata from the given protocol in xml file
        and then from that automata, generates presburger formula type input to be solved by smt solver*/
        Constraint(const char* path, std::unordered_map<string, vector<string> > bad_c, int bound, string channel_type, string semantics)
        {
            bad = bad_c;
            num_asserts = 0;

            c_time = clock();
            //call to the constructor of class CommunicatingProcess which generates automata for the given protocol
            CommunicatingProcess cprocess(path, channel_type);
            c_time = clock() - c_time;

            //copying details of generated automata into the private members of class Constraint
            unique = cprocess.get_unique_no();
            Processes = cprocess.get_Processes();
            Process_state_name = cprocess.get_Process_state_name();
            Process_transition_message = cprocess.get_Process_transition_message();
            Process_transition_symbol = cprocess.get_Process_transition_symbol();
            Process_channel = cprocess.get_PChannels();
            Process_initial_state = cprocess.get_Process_initial_state();
            Process_final_state = cprocess.get_Process_final_state();
            Aut_messages = cprocess.get_Aut_messages();
            Process_roles = cprocess.get_Process_roles();
            Channels = cprocess.get_Channels();
            Connc_comp_map = cprocess.get_Connc_comp_map();

            //checking whether the data contained in bad_c is legitimate or not with respect to given protocol
            check_validity();
            //call to the constructor of class Constraint which from the above generated automata generates presburger formula type input to be solved by smt solver 
            generate(cprocess, bound, semantics, channel_type);
        }

        /*Class Constraint constructor which generates presburger formula type input to be solved by smt solver
        for the given semantics of the given protocol*/
        void generate(CommunicatingProcess cprocess, int bound, string semantics, string channel_type)
        {          
            clock_t t=clock();

            for(int i=0,j=1;i<Processes.size();i=i+2,j=j+2)
                query += generate_variables_declaration(cprocess, Processes[i], Processes[j], Process_state_name[i], Process_state_name[j], Process_transition_symbol[i], Process_transition_symbol[j], Process_transition_message[i], Process_transition_message[j], bound, Process_final_state[i], Process_final_state[j]);

            for(int i=0,j=1;i<Processes.size();i=i+2,j=j+2)
                query += generate_in_and_out_flow_constraints(cprocess, Processes[i], Processes[j], Process_transition_symbol[i], Process_transition_symbol[j], Process_transition_message[i], Process_transition_message[j], Process_state_name[i], Process_state_name[j], (((*(Process_state_name[i]))[Process_initial_state[i]]) + "_1"), bound, Process_final_state[i], Process_final_state[j]);

            query += enforce_distinct_index(bound);
            
            if(semantics == "unordered")
            {
                query += enforcing_receive_transitions_matching(cprocess, bound, channel_type);
                query += enforcing_unordered_computation_order_for_transitions_pair_per_channel(cprocess, bound, channel_type);
            }

            if(semantics == "lossy")
            {
                query += enforcing_receive_transitions_matching(cprocess, bound, channel_type);
                query += enforcing_lossy_computation_order_for_transitions_pair_per_channel(cprocess, bound, channel_type);
            }

            if(semantics == "stuttering")
            {
                query += enforcing_receive_transitions_matching(cprocess, bound, channel_type);
                query += enforcing_stuttering_computation_order_for_transitions_pair_per_channel(cprocess, bound, channel_type);
            }

            t=clock() - t;
            c_time = c_time + t;
        }

        //Checking whether the data contained in bad_c is legitimate or not with respect to given protocol
        void check_validity()
        {
            bool flag = false, flag1 = false;
            for(auto it = bad.begin(); it != bad.end() ; ++it)
            {
                int i;

                for(i=1;i<Processes.size();i=i+2)
                    if(((*(Process_state_name[i]))[Process_final_state[i]]).substr(0, (it->first).size()) == (it->first))
                    {
                        flag = true;
                        break;
                    }

                if(flag == false)
                {
                    cout<<endl<<"Role not found !"<<endl<<"Exiting";
                    exit(0);
                }
                    
                for(int j =0; j < (it->second).size();++j)
                {
                    Process_pointer process = Processes[i];

                    for(ListDigraph::NodeIt ni(*process); ni != INVALID ; ++ni)
                        if(((*(Process_state_name[i]))[ni]).find((it->second)[j]) != ((*(Process_state_name[i]))[ni]).npos)
                            flag1 = true;

                    if(flag1 == false)
                    {
                        cout<<endl<<(it->second)[j]<<" state not found!"<<endl<<"Exiting"<<endl;
                        exit(0);
                    }
                    else
                        flag1 = false;
                }   
            }
        }

        //Return the number of assertions generated while generating input to the solved by smt solver
        int get_number_of_assertions()
        {
            return num_asserts;
        }

        //Return the number of unique transtitions generated while generating automata
        int get_unique_no()
        {
            return unique;
        }

        //Return the input generated which will then be solved by smt solver
        string get_query()
        {
            return query;
        }

        //Return the number of states generated while generating automata
        int get_no_states()
        {
            int k = 0;
            for(int i=0;i<Processes.size();++i)
                for(ListDigraph::NodeIt ni(*(Processes[i])); ni != INVALID; ++ni)
                    ++k;

            return k;
        }

        //Return the total time taken while generating automata and input to the solved by smt solver 
        clock_t get_constraint_automata_generation_time()
        {
            return c_time;
        }

        /*Return the tuple containing index, match and occurence variables of all those receive transitions which have
        "msg" as their symbol*/
        vector<vector<string> > get_i_var_o_var_m_var_triples_for_msg(CommunicatingProcess cprocess, Process_pointer process, Nname_pointer state_name, Avalues_pointer transition_symbol, Avalues_pointer transition_message, Cvalue_pointer transition_channel, string msg, int range, string channel, string channel_type)
        {
            vector<vector<string> > receive;
            vector<string> dummy;

            vector<ListDigraph::Arc> trans = cprocess.get_transitions(process);
            int i, j, count = 0;
            for(i=0;i<trans.size();i++)
            {
                if((*transition_symbol)[trans[i]] == msg)
                {
                    if(channel_type != "xml")
                        goto jump;
                    if((*transition_channel)[trans[i]] == channel)
                    {
                        jump:;
                        for(j=1;j<=range;j++)
                        {
                            stringstream result;
                            result << j;
                            receive.push_back(dummy);

                            receive[count*range+j-1].push_back("i_" + (*state_name)[(process->source(trans[i]))] + "_" + result.str() + "_" + (*transition_message)[trans[i]] + "_" + (*transition_symbol)[trans[i]] + "_" + (*state_name)[(process->target(trans[i]))] + "_" + result.str());
                            receive[count*range+j-1].push_back("o_" + (*state_name)[(process->source(trans[i]))] + "_" + result.str() + "_" + (*transition_message)[trans[i]]+ "_" + (*transition_symbol)[trans[i]] + "_" + (*state_name)[(process->target(trans[i]))] + "_" + result.str());
                            receive[count*range+j-1].push_back("m_" + (*state_name)[(process->source(trans[i]))] + "_" + result.str() + "_" + (*transition_message)[trans[i]] + "_" + (*transition_symbol)[trans[i]] + "_" + (*state_name)[(process->target(trans[i]))] + "_" + result.str());
                        }
                        count++;
                    }
                }
            }

            return receive;
        }

        /*Return the tuple containing index and occurence variables of all those send transitions which have
        "msg" as their symbol*/
        vector<vector<string> > get_i_var_o_var_pairs_for_send_of_msg(CommunicatingProcess cprocess, Process_pointer process, Nname_pointer state_name, Avalues_pointer transition_symbol, Avalues_pointer transition_message, Cvalue_pointer transition_channel, string msg, int range, string channel, string channel_type)
        {
            vector<vector<string> > send;
            vector<string> dummy;
            vector<ListDigraph::Arc> trans = cprocess.get_transitions(process);
            int i, j, count = 0;

            for(i=0;i<trans.size();i++)
            {
                if((*transition_symbol)[trans[i]] == msg || ((*transition_symbol)[trans[i]]).find(msg) != ((*transition_symbol)[trans[i]]).npos)
                {
                    string temp_m = (*transition_symbol)[trans[i]];
                    char* t1 = new char[temp_m.length() + 1];
                    strcpy(t1,temp_m.c_str());
                    string temp_c = (*transition_channel)[trans[i]];
                    char* t2 = new char[temp_c.length() + 1];
                    strcpy(t2,temp_c.c_str());

                    unordered_set<string> chnl_filter;
                    unordered_set<string>::iterator it;
                    char *p1 = strtok(t1,"$$");

                    vector<string> msg_s;
                    vector<string> channel_s;
                    while( p1 != NULL)
                    {
                        msg_s.push_back(string(p1));
                        p1 = strtok(NULL,"$$");
                    }
                    char *p2 = strtok(t2,"$$");
                    while(p2 != NULL)
                    {
                        channel_s.push_back(string(p2));
                        p2 = strtok(NULL,"$$");
                    }
                    for(j=0;j<msg_s.size();j++)
                    {
                        if(msg_s[j] == msg)
                        chnl_filter.insert(channel_s[j]);
                    }

                    if(channel_type != "xml")
                        goto jump;

                    for(it = chnl_filter.begin(); it != chnl_filter.end();++it)
                    {
                        if(*it != channel)
                            continue;
                        else
                        {
                            jump:;
                            for(j=1;j<=range;j++)
                            {
                                stringstream result;
                                result << j;
                                send.push_back(dummy);

                                if(cprocess.check_unique(trans[i],process,state_name))
                                {
                                    send[count*range+j-1].push_back("i_l_" + (*state_name)[(process->source(trans[i]))] + "_" + result.str() + "_" + (*transition_message)[trans[i]] + "_" + (*transition_symbol)[trans[i]] + "_" + (*state_name)[(process->target(trans[i]))] + "_" + result.str());
                                    send[count*range+j-1].push_back("i_r_" + (*state_name)[(process->source(trans[i]))] + "_" + result.str() + "_" + (*transition_message)[trans[i]] + "_" + (*transition_symbol)[trans[i]] + "_" + (*state_name)[(process->target(trans[i]))] + "_" + result.str());
                                    send[count*range+j-1].push_back("o_" + (*state_name)[(process->source(trans[i]))] + "_" + result.str() + "_" + (*transition_message)[trans[i]] + "_" + (*transition_symbol)[trans[i]] + "_" + (*state_name)[(process->target(trans[i]))] + "_" + result.str());
                                }
                                else
                                {
                                    send[count*range+j-1].push_back("i_" + (*state_name)[(process->source(trans[i]))]+ "_" + result.str() + "_" + (*transition_message)[trans[i]] + "_" + (*transition_symbol)[trans[i]] + "_" + (*state_name)[(process->target(trans[i]))] + "_" + result.str());
                                    send[count*range+j-1].push_back("o_" + (*state_name)[(process->source(trans[i]))] + "_" + result.str() + "_" + (*transition_message)[trans[i]] + "_" + (*transition_symbol)[trans[i]] + "_" + (*state_name)[(process->target(trans[i]))] + "_" + result.str());
                                }
                            }
                            count++;
                            break;
                        }
                    }
                }
            }

            return send;
        }

        //Return the vector containing index of all those transitions which have their target state as "state"
        vector<string> get_in_i_vars(CommunicatingProcess cprocess, Process_pointer process, Process_pointer process_needed, Nname_pointer state_name, Nname_pointer state_name_needed, Avalues_pointer transition_symbol, Avalues_pointer transition_message, Avalues_pointer transition_symbol_needed, Avalues_pointer transition_message_needed, string state, int phase, int range,ListDigraph::Node final_state, ListDigraph::Node final_state_needed)
        {
            vector<string> in_i_var;
            stringstream result, result3;
            result << phase;
            int i, j, m;
            m = phase-1;
            result3 << m;

            vector<string> states = cprocess.get_states(process,state_name);
            for(i=0;i<states.size();i++)
                if(state == states[i])
                    goto jump1;

            cout << state << " not a valid state " << "\n";
            goto jump;

            jump1:
            {
                vector<ListDigraph::Arc> trans = cprocess.get_transitions(process);

                //adds index of those transitions present in automata and have "state" as its target state
                for(i=0;i<trans.size();i++)
                    if((*state_name)[(process->target(trans[i]))] == state)
                            in_i_var.push_back("o_" + (*state_name)[(process->source(trans[i]))]+ "_" + result.str() + "_" + (*transition_message)[trans[i]] + "_" + (*transition_symbol)[trans[i]]  + "_" + (*state_name)[(process->target(trans[i]))] + "_" + result.str());

                //adds index of those transitions going from R to S copy and have "state" as its target state
                if(   (phase!=1) && (state.substr(state.length()-2,state.length())  ==   "_S")   )
                {
                    if(cprocess.check_unique_state(state))
                    {
                        string temp = state.substr(4, state.length());
                        char dummy[temp.length()];
                        strcpy(dummy, temp.c_str());
                        char *token;
                        token = strtok(dummy, "$$");
                        vector<string> SCCstates; //states vector containing all SCC state present in this state
                        while (token != NULL)
                        {
                            SCCstates.push_back(token);
                            token = strtok(NULL, "$$");
                        }
                        for(i=0;i<SCCstates.size();i++)
                            in_i_var.push_back("o_" + SCCstates[i].substr(0,SCCstates[i].length()-2) + "_R_" + result3.str() + "_eps_eps_" + state + "_" + result.str());
                    }
                    else
                    {
                        if(state != (*state_name)[final_state])
                            in_i_var.push_back("o_" + state.substr(0,state.length()-2) + "_R_" + result3.str() + "_eps_eps_" + state + "_" + result.str());
                    }
                }

                //adds index of those transitions going from S to R copy and have "state" as its target state
                if(state.substr(state.length()-2,state.length())  ==   "_R")
                {
                    if(Connc_comp_map.find(state) != Connc_comp_map.end())
                    {
                        vector<string> needstates = cprocess.get_states(process_needed,state_name_needed);
                        for(i=0;i<needstates.size();i++)
                            if((needstates[i]).find(state.substr(0,state.length()-2) + "_S") != (needstates[i]).npos)
                                in_i_var.push_back("o_" + needstates[i] + "_" + result.str() + "_eps_eps_" + state + "_" + result.str());
                    }
                    else
                    {
                        if(state != (*state_name)[final_state])
                            in_i_var.push_back("o_" + state.substr(0,state.length()-2) + "_S_" + result.str() + "_eps_eps_" + state + "_" + result.str());
                    }

                    //adds index of those transitions going to final state in the R copy of the last phase
                    if((state == (*state_name)[final_state]) && phase == range)
                    {
                        vector<string> states_receive = cprocess.get_states(process,state_name);
                        auto it = bad.begin();
                        for(;it != bad.end();++it)
                        {
                            if(((*state_name)[final_state]).substr(0, (it->first).size()) != (it->first))
                                continue;
                            else
                                goto jump2;
                        }

                        for(j=0;j<states_receive.size();j++)
                            if(states_receive[j] != (*state_name)[final_state])
                                in_i_var.push_back("o_" + states_receive[j] + "_" + result.str() + "_eps_eps_" + state + "_" + result.str());

                        goto jump3;
                        jump2:

                        for(j=0;j<states_receive.size();j++)
                            for(i=0;i<(it->second).size();i++)
                                if(states_receive[j].find((it->second)[i]+"_R") != (states_receive[j]).npos)
                                    in_i_var.push_back("o_" + states_receive[j] + "_" + result.str() + "_eps_eps_" + state + "_" + result.str());
                        jump3:;
                    }
                }
            }
            jump:
            return in_i_var;
        }

        //Return the vector containing index of all those transitions which have their source state as "state"
        vector<string> get_out_i_vars(CommunicatingProcess cprocess, Process_pointer process, Process_pointer process_needed, Nname_pointer state_name, Nname_pointer state_name_needed, Avalues_pointer transition_symbol, Avalues_pointer transition_message, Avalues_pointer transition_symbol_needed, Avalues_pointer transition_message_needed, string state, int phase, int range,ListDigraph::Node final_state, ListDigraph::Node final_state_needed)
        {
            vector<string> out_i_var;
            stringstream result, result3;
            result << phase;
            int i, m;
            m = phase+1;
            result3 << m;

            vector<string> states = cprocess.get_states(process,state_name);
            for(i=0;i<states.size();i++)
                if(state == states[i])
                    goto jump1;

            cout << state << " not a valid state " << "\n";
            goto jump;

            jump1:
            {
                vector<ListDigraph::Arc> trans = cprocess.get_transitions(process);

                //adds index of those transitions present in automata and have "state" as its source state
                for(i=0;i<trans.size();i++)
                    if((*state_name)[(process->source(trans[i]))]  == state)
                        out_i_var.push_back("o_" + (*state_name)[(process->source(trans[i]))] + "_" + result.str() + "_" + (*transition_message)[trans[i]]  + "_" + (*transition_symbol)[trans[i]]  + "_" + (*state_name)[(process->target(trans[i]))] + "_" + result.str());
                        
                //adds index of those transitions going from R to S copy and have "state" as its source state
                if(   (phase!=range) && (state.substr(state.length()-2,state.length())  ==   "_R")   )
                {
                    if(Connc_comp_map.find(state) != Connc_comp_map.end())
                    {
                        vector<string> needstates = cprocess.get_states(process_needed,state_name_needed);
                        for(i=0;i<needstates.size();i++)
                            if((needstates[i]).find(state.substr(0, state.length()-2) + "_S") != (needstates[i]).npos)
                                out_i_var.push_back("o_" + state + "_" + result.str() + "_eps_eps_" + needstates[i] + "_" + result3.str());
                    }
                    else
                    {
                        if(state != (*state_name)[final_state])
                            out_i_var.push_back("o_" + state + "_" + result.str() + "_eps_eps_" + state.substr(0,state.length()-2) + "_S_" + result3.str());
                    }
                }

                //adds index of those transitions going from "state" to final state in the R copy of the last phase
                if(state != (*state_name)[final_state] && (phase == range) && ((state.substr(state.length()-2,state.length())  ==   "_R")))
                {
                    auto it = bad.begin();
                    for(;it != bad.end();++it)
                    {
                        if(((*state_name)[final_state]).substr(0, (it->first).size()) != (it->first))
                            continue;
                        else
                            goto jump2;
                    }
                    out_i_var.push_back("o_" + state + "_" + result.str() + "_eps_eps_" + (*state_name)[final_state] + "_" + result.str());
                    goto jump3;

                    jump2:
                    for(int i=0;i < (it->second).size();i++)
                        if(state.find(((it->second)[i] + "_R")) != (state).npos)
                            out_i_var.push_back("o_" + state + "_" + result.str() + "_eps_eps_" + (*state_name)[final_state] + "_" + result.str());

                    jump3:;
                }

                //adds index of those transitions going from S to R copy and have "state" as its source state
                if(state.substr(state.length()-2,state.length())  ==   "_S")
                {
                    if(cprocess.check_unique_state(state))
                    {
                        string temp = state.substr(4, state.length());
                        char dummy[temp.length()];
                        strcpy(dummy, temp.c_str());
                        char *token;
                        token = strtok(dummy, "$$");
                        vector<string> SCCstates; //states vector containing all SCC state present in this state
                        while (token != NULL)
                        {
                            SCCstates.push_back(token);
                            token = strtok(NULL, "$$");
                        }
                        for(i=0;i<SCCstates.size();i++)
                            out_i_var.push_back("o_" + state + "_" + result.str() + "_eps_eps_" + SCCstates[i].substr(0,SCCstates[i].length()-2) + "_R_" + result.str());
                    }
                    else
                    {
                        if(state != (*state_name)[final_state])
                            out_i_var.push_back("o_" + state + "_" + result.str() + "_eps_eps_" + state.substr(0,state.length()-2) + "_R_" + result.str());
                    }   
                }
            }
            jump:
            return out_i_var;
        }

        //Declaring variables such as index, match and occurence variable for each transition
        string generate_variables_declaration(CommunicatingProcess cprocess, Process_pointer process_send, Process_pointer process_receive, Nname_pointer state_name_send, Nname_pointer state_name_receive, Avalues_pointer transition_symbol_send, Avalues_pointer transition_symbol_receive, Avalues_pointer transition_message_send, Avalues_pointer transition_message_receive, int bound, ListDigraph::Node final_state_send, ListDigraph::Node final_state_receive)
        {
            string decls;
            int i, j, l, m;

            decls += "; declaring index and occurence variables for send transitions \n";
            cout << "; declaring index and occurence variables for send transitions \n";

            //Declaring index and occurence variables for send transitions
            vector<ListDigraph::Arc> trans = cprocess.get_transitions(process_send);
            for(j=0;j<trans.size();j++)
            {
                if(cprocess.check_unique(trans[j], process_send, state_name_send))
                {
                    for(l=1;l<=bound;l++)
                    {
                        stringstream result1;
                        result1 << l;
                        decls += "(declare-fun i_l_" + (*state_name_send)[(process_send->source(trans[j]))] + "_" + result1.str() + "_" + (*transition_message_send)[trans[j]] + "_" + (*transition_symbol_send)[trans[j]]  + "_" + (*state_name_send)[(process_send->target(trans[j]))] + "_" + result1.str() + " () Int) \n" + create_assertion(create_statement(">=", "i_l_" + (*state_name_send)[(process_send->source(trans[j]))] + "_" + result1.str() + "_" + (*transition_message_send)[trans[j]] + "_" + (*transition_symbol_send)[trans[j]]+ "_" +(*state_name_send)[ (process_send->target(trans[j]))] + "_" + result1.str(), "0"));
                        decls += "(declare-fun i_r_" + (*state_name_send)[(process_send->source(trans[j]))]+ "_" + result1.str() + "_" + (*transition_message_send)[trans[j]] + "_" + (*transition_symbol_send)[trans[j]] + "_" + (*state_name_send)[(process_send->target(trans[j]))] + "_" + result1.str() + " () Int) \n" + create_assertion(create_statement(">=", "i_r_" + (*state_name_send)[(process_send->source(trans[j]))] + "_" + result1.str() + "_" + (*transition_message_send)[trans[j]] + "_" + (*transition_symbol_send)[trans[j]] + "_" + (*state_name_send)[(process_send->target(trans[j]))] + "_" + result1.str(), "0"));
                        decls += create_assertion(create_statement(">=", "i_r_" + (*state_name_send)[(process_send->source(trans[j]))] + "_" + result1.str() + "_" + (*transition_message_send)[trans[j]]+ "_" + (*transition_symbol_send)[trans[j]] + "_" + (*state_name_send)[(process_send->target(trans[j]))] + "_" + result1.str(), "i_l_" + (*state_name_send)[(process_send->source(trans[j]))] + "_" + result1.str() + "_" + (*transition_message_send)[trans[j]]  + "_" + (*transition_symbol_send)[trans[j]] + "_" + (*state_name_send)[(process_send->target(trans[j]))] + "_" + result1.str()));
                        decls += "(declare-fun o_" + (*state_name_send)[(process_send->source(trans[j]))] + "_" + result1.str() + "_" + (*transition_message_send)[trans[j]]+ "_" + (*transition_symbol_send)[trans[j]] + "_" + (*state_name_send)[(process_send->target(trans[j]))] + "_" + result1.str() + " () Int) \n" + create_assertion(create_statement(">=", "o_" + (*state_name_send)[(process_send->source(trans[j]))] + "_" + result1.str() + "_" + (*transition_message_send)[trans[j]]  + "_" + (*transition_symbol_send)[trans[j]]+ "_" + (*state_name_send)[(process_send->target(trans[j]))] + "_" + result1.str(), "0"));
                    }
                }
                else
                {
                    for(l=1;l<=bound;l++)
                    {
                        stringstream result1;
                        result1 << l;
                        decls += "(declare-fun i_" + (*state_name_send)[(process_send->source(trans[j]))] + "_" + result1.str() + "_" + (*transition_message_send)[trans[j]] + "_" + (*transition_symbol_send)[trans[j]] + "_" + (*state_name_send)[(process_send->target(trans[j]))] + "_" + result1.str() + " () Int) \n" + create_assertion(create_statement(">=", "i_" + (*state_name_send)[(process_send->source(trans[j]))] + "_" + result1.str() + "_" + (*transition_message_send)[trans[j]]  + "_" + (*transition_symbol_send)[trans[j]] + "_" + (*state_name_send)[(process_send->target(trans[j]))]+ "_" + result1.str(), "0"));
                        decls += "(declare-fun o_" + (*state_name_send)[(process_send->source(trans[j]))]+ "_" + result1.str() + "_" + (*transition_message_send)[trans[j]] + "_" + (*transition_symbol_send)[trans[j]] + "_" + (*state_name_send)[(process_send->target(trans[j]))] + "_" + result1.str() + " () Int) \n" + create_assertion(create_statement(">=", "o_" + (*state_name_send)[(process_send->source(trans[j]))] + "_" + result1.str() + "_" + (*transition_message_send)[trans[j]]  + "_" + (*transition_symbol_send)[trans[j]] + "_" + (*state_name_send)[(process_send->target(trans[j]))] + "_" + result1.str(), "0"));
                        global_i_vars.push_back("i_" + (*state_name_send)[(process_send->source(trans[j]))]+ "_" + result1.str() + "_" + (*transition_message_send)[trans[j]] + "_" + (*transition_symbol_send)[trans[j]] + "_" + (*state_name_send)[(process_send->target(trans[j]))]+ "_" + result1.str());
                    }
                }
            }

            decls += "; declaring index, occurence and match variables for receive transitions \n";
            cout << "; declaring index, occurence and match variables for receive transitions \n";

            //Declaring index, occurence and match variables for receive transitions
            trans = cprocess.get_transitions(process_receive);
            for(j=0;j<trans.size();j++)
            {
                for(l=1;l<=bound;l++)
                {
                    stringstream result1;
                    result1 << l;
                    decls += "(declare-fun i_" + (*state_name_receive)[(process_receive->source(trans[j]))] + "_" + result1.str() + "_" + (*transition_message_receive)[trans[j]] + "_" + (*transition_symbol_receive)[trans[j]] + "_" + (*state_name_receive)[(process_receive->target(trans[j]))]+ "_" + result1.str() + " () Int) \n" + create_assertion(create_statement(">=", "i_" + (*state_name_receive)[(process_receive->source(trans[j]))] + "_" + result1.str() + "_" + (*transition_message_receive)[trans[j]] + "_" +(*transition_symbol_receive)[trans[j]] + "_" + (*state_name_receive)[(process_receive->target(trans[j]))] + "_" + result1.str(), "0"));                              
                    decls += "(declare-fun o_" + (*state_name_receive)[(process_receive->source(trans[j]))] + "_" + result1.str() + "_" + (*transition_message_receive)[trans[j]] + "_" + (*transition_symbol_receive)[trans[j]] + "_" + (*state_name_receive)[(process_receive->target(trans[j]))] + "_" + result1.str() + " () Int) \n" + create_assertion(create_statement(">=", "o_" +(*state_name_receive) [(process_receive->source(trans[j]))] + "_" + result1.str() + "_" + (*transition_message_receive)[trans[j]] + "_" + (*transition_symbol_receive)[trans[j]]+ "_" + (*state_name_receive)[(process_receive->target(trans[j]))] + "_" + result1.str(), "0"));
                    decls += "(declare-fun m_" + (*state_name_receive)[(process_receive->source(trans[j]))]+ "_" + result1.str() + "_" + (*transition_message_receive)[trans[j]] + "_" + (*transition_symbol_receive)[trans[j]] + "_" + (*state_name_receive)[(process_receive->target(trans[j]))] + "_" + result1.str() + " () Int) \n" + create_assertion(create_statement(">=", "m_" + (*state_name_receive)[(process_receive->source(trans[j]))] + "_" + result1.str() + "_" + (*transition_message_receive)[trans[j]] + "_" + (*transition_symbol_receive)[trans[j]] + "_" + (*state_name_receive)[(process_receive->target(trans[j]))]+ "_" + result1.str(), "0"));
                    global_i_vars.push_back("i_" + (*state_name_receive)[(process_receive->source(trans[j]))] + "_" + result1.str() + "_" + (*transition_message_receive)[trans[j]] + "_" + (*transition_symbol_receive)[trans[j]] + "_" + (*state_name_receive)[(process_receive->target(trans[j]))] + "_" + result1.str());
                }
            }
            
            decls += "; declaring index and occurence variables for eps transitions between two phases \n";
            cout << "; declaring index and occurence variables for eps transitions between two phases \n";

            //Declaring index and occurence variables for eps transitions between two phases
            vector<string> states = cprocess.get_states(process_send,state_name_send);
            for(j=0;j<states.size();j++)
            {
                for(l=1;l<=bound;l++)
                {
                    stringstream result;
                    result << l;

                    if(l!=1)
                    {
                        m = l-1;
                        stringstream result1;
                        result1 << m;
                        if(cprocess.check_unique_state(states[j]))
                        {
                            string temp = states[j].substr(4, states[j].length());
                            char dummy[temp.length()];
                            strcpy(dummy, temp.c_str());
                            char *token;
                            token = strtok(dummy, "$$");
                            vector<string> SCCstate;
                            while (token != NULL)
                            {
                                SCCstate.push_back(token);
                                token = strtok(NULL, "$$");
                            }

                            for(i=0;i<SCCstate.size();i++)
                            {
                                decls += "(declare-fun o_" + SCCstate[i].substr(0,SCCstate[i].length()-2) + "_R_" + result1.str() + "_eps_eps_" + states[j] + "_" + result.str() + " () Int) \n" + create_assertion(create_statement(">=", "o_" + SCCstate[i].substr(0,SCCstate[i].length()-2) + "_R_" + result1.str() + "_eps_eps_" + states[j] + "_" + result.str(), "0"));
                                decls += "(declare-fun i_" + SCCstate[i].substr(0,SCCstate[i].length()-2) + "_R_" + result1.str() + "_eps_eps_" + states[j] + "_" + result.str() + " () Int) \n" + create_assertion(create_statement(">=", "i_" + SCCstate[i].substr(0,SCCstate[i].length()-2) + "_R_" + result1.str() + "_eps_eps_" + states[j] + "_" + result.str(), "0"));
                                global_i_vars.push_back("i_" + SCCstate[i].substr(0,SCCstate[i].length()-2) + "_R_" + result1.str() + "_eps_eps_" + states[j] + "_" + result.str());
                            }
                        }
                        else
                        {
                            if(states[j] != (*state_name_send)[final_state_send])
                            {
                                decls += "(declare-fun o_" + states[j].substr(0,states[j].length()-2) + "_R_" + result1.str() + "_eps_eps_" + states[j] + "_" + result.str() + " () Int) \n" + create_assertion(create_statement(">=", "o_" + states[j].substr(0,states[j].length()-2) + "_R_" + result1.str() + "_eps_eps_" + states[j] + "_" + result.str(), "0"));
                                decls += "(declare-fun i_" + states[j].substr(0,states[j].length()-2) + "_R_" + result1.str() + "_eps_eps_" + states[j] + "_" + result.str() + " () Int) \n" + create_assertion(create_statement(">=", "i_" + states[j].substr(0,states[j].length()-2) + "_R_" + result1.str() + "_eps_eps_" + states[j] + "_" + result.str(), "0"));
                                global_i_vars.push_back("i_" + states[j].substr(0,states[j].length()-2) + "_R_" + result1.str() + "_eps_eps_" + states[j] + "_" + result.str());
                            }
                        }
                    }
                }
            }

            states = cprocess.get_states(process_receive,state_name_receive);
            for(j=0;j<states.size();j++)
            {
                for(l=1;l<=bound;l++)
                {
                    stringstream result;
                    result << l;

                    if(Connc_comp_map.find(states[j]) != Connc_comp_map.end())
                    {
                        vector<string> needstates = cprocess.get_states(process_send,state_name_send);
                        for(i=0;i<needstates.size();i++)
                            if((needstates[i]).find(states[j].substr(0,states[j].length()-2) + "_S") != (needstates[i]).npos)
                            {
                                decls += "(declare-fun o_" + needstates[i] + "_" + result.str() + "_eps_eps_" + states[j] + "_" + result.str() + " () Int) \n" + create_assertion(create_statement(">=", "o_" + needstates[i] + "_" + result.str() + "_eps_eps_" + states[j] + "_" + result.str(), "0"));
                                decls += "(declare-fun i_" + needstates[i] + "_" + result.str() + "_eps_eps_" + states[j] + "_" + result.str() + " () Int) \n" + create_assertion(create_statement(">=", "i_" + needstates[i] + "_" + result.str() + "_eps_eps_" + states[j] + "_" + result.str(), "0"));
                                global_i_vars.push_back("i_" + needstates[i] + "_" + result.str() + "_eps_eps_" + states[j] + "_" + result.str());
                            }
                    }
                    else
                    {
                        if(states[j] != (*state_name_receive)[final_state_receive])
                        {
                            decls += "(declare-fun o_" + states[j].substr(0,states[j].length()-2) + "_S_" + result.str() + "_eps_eps_" + states[j] + "_" + result.str() + " () Int) \n" + create_assertion(create_statement(">=", "o_" + states[j].substr(0,states[j].length()-2) + "_S_" + result.str() + "_eps_eps_" + states[j] + "_" + result.str(), "0"));
                            decls += "(declare-fun i_" + states[j].substr(0,states[j].length()-2) + "_S_" + result.str() + "_eps_eps_" + states[j] + "_" + result.str() + " () Int) \n" + create_assertion(create_statement(">=", "i_" + states[j].substr(0,states[j].length()-2) + "_S_" + result.str() + "_eps_eps_" + states[j] + "_" + result.str(), "0"));
                            global_i_vars.push_back("i_" + states[j].substr(0,states[j].length()-2) + "_S_" + result.str() + "_eps_eps_" + states[j] + "_" + result.str());
                        }
                    }

                    if(l == bound and states[j] != (*state_name_receive)[final_state_receive])
                    {
                        auto it = bad.begin();
                        for(;it != bad.end();++it)
                        {
                            if(((*state_name_receive)[final_state_receive]).substr(0, (it->first).size()) != (it->first))
                                continue;
                            else
                                goto jump1;
                        }

                        decls += "(declare-fun o_" + states[j] + "_" + result.str() + "_eps_eps_" + (*state_name_receive)[final_state_receive] + "_" + result.str() + " () Int) \n" + create_assertion(create_statement(">=", "o_" + states[j] + "_" + result.str() + "_eps_eps_" + (*state_name_receive)[final_state_receive] + "_" + result.str(), "0"));
                        decls += "(declare-fun i_" + states[j] + "_" + result.str() + "_eps_eps_" + (*state_name_receive)[final_state_receive] + "_" + result.str() + " () Int) \n" + create_assertion(create_statement(">=", "i_" + states[j] + "_" + result.str() + "_eps_eps_" + (*state_name_receive)[final_state_receive] + "_" + result.str(), "0"));
                        global_i_vars.push_back("i_" + states[j] + "_" + result.str() + "_eps_eps_" + (*state_name_receive)[final_state_receive] + "_" + result.str());
                        goto jump;

                        jump1:
                        for(int i=0;i<(it->second).size();i++)
                            if(states[j].find((it->second)[i]+"_R") != (states[j]).npos)
                            {
                                decls += "(declare-fun o_" + states[j] + "_" + result.str() + "_eps_eps_" + (*state_name_receive)[final_state_receive] + "_" + result.str() + " () Int) \n" + create_assertion(create_statement(">=", "o_" + states[j] + "_" + result.str() + "_eps_eps_" + (*state_name_receive)[final_state_receive] + "_" + result.str(), "0"));
                                decls += "(declare-fun i_" + states[j] + "_" + result.str() + "_eps_eps_" + (*state_name_receive)[final_state_receive] + "_" + result.str() + " () Int) \n" + create_assertion(create_statement(">=", "i_" + states[j] + "_" + result.str() + "_eps_eps_" + (*state_name_receive)[final_state_receive] + "_" + result.str(), "0"));
                                global_i_vars.push_back("i_" + states[j] + "_" + result.str() + "_eps_eps_" + (*state_name_receive)[final_state_receive] + "_" + result.str());
                            }   
                        jump:;
                    }
                }
            }
            return decls;
        }

        //Ensuring that each non-unique transitions have different index varibles
        string enforce_distinct_index(int bound)
        {
            string glob_enum("");
            string equal_index, distinct_index;
            vector<vector<string> >temp;
            vector<string> dummy;
            int i, j;

            glob_enum += "; declaring distinct index condition for each pair of non unique transitions \n";
            cout << "; declaring distinct index condition for each pair of non unique transitions \n";
            glob_enum += create_assertion(create_distinct_statement(global_i_vars));
            
            return glob_enum;
        }

        /*Ensuring several contraints such as:
        1: in flow sum is equal to out flow sum for every state which is neither initial state not final state
        2: in flow sum sum is one less than the out flow sum for the initial state
        3: in flow sum is one more than the out flow sum for the final state
        4: for each state, if its in flow sum > 0, then this implies that ther is atleast one transitions having this
        state as its target state whose occurence varible > 0 and its index variable is less than the index variable
        of another transition having its source state as this state and its ocuurence variable also greater than 0*/
        string generate_in_and_out_flow_constraints(CommunicatingProcess cprocess, Process_pointer process_send, Process_pointer process_receive, Avalues_pointer transition_symbol_send, Avalues_pointer transition_symbol_receive, Avalues_pointer transition_message_send, Avalues_pointer transition_message_receive, Nname_pointer state_name_send, Nname_pointer state_name_receive, string init, int bound, ListDigraph::Node final_state_send, ListDigraph::Node final_state_receive)
        {
            string in_out_enforcement(""), in_flow_sum;
            stringstream result;
            result << bound;
            int i, j, l, m;

            for(i=0;i<(cprocess.get_states(process_send,state_name_send)).size();i++)
                if(init == ((cprocess.get_states(process_send,state_name_send))[i] + "_1"))
                    goto jump;

            cout << ("; initial state not recognized: " + init + "\n");
            return ("; initial state not recognized: " + init + "\n");
            goto jump2;

            jump:
            for(i=0;i<(cprocess.get_states(process_receive,state_name_receive)).size();i++)
                if((*state_name_receive)[final_state_receive] + "_" + result.str() == ((cprocess.get_states(process_receive,state_name_receive))[i] + "_" + result.str()))
                    goto jump1;

            cout << ("; final state not recognized: " + (*state_name_receive)[final_state_receive] + "result.str()" + "\n");
            return ("; final state not recognized: " + (*state_name_receive)[final_state_receive] + "result.str()" + "\n");
            goto jump2;
            
            jump1:
            {
                vector<string> in_vars, out_vars;
                   
                in_out_enforcement += "; adding in and out flow constraint \n";
                cout << ("; adding in and out flow constraint \n");

                //states vector containing states in send copy
                vector<string> states = (cprocess.get_states(process_send,state_name_send));
                for(i=0;i<states.size();i++)
                {
                    for(j=1;j<=bound;j++)
                    {
                        stringstream result1;
                        result1 << j;
                        in_out_enforcement += "; constraint of state " + states[i] + "_" + result1.str() + " \n";
                        //cout << ("; constraint of state " + states[i] + "_" + result1.str() + " \n");
                        in_vars = get_in_i_vars(cprocess, process_send, process_receive, state_name_send, state_name_receive, transition_symbol_send, transition_message_send, transition_symbol_receive, transition_message_receive, states[i], j, bound,final_state_send, final_state_receive);
                        out_vars = get_out_i_vars(cprocess, process_send, process_receive, state_name_send, state_name_receive, transition_symbol_send, transition_message_send, transition_symbol_receive, transition_message_receive, states[i], j, bound,final_state_send, final_state_receive);
                        in_out_enforcement += create_assertion(create_statement("<=", create_sum(in_vars), "1"));
                        if((states[i] + "_" + result1.str()) == init)
                        {
                            in_vars.push_back("1");
                            in_out_enforcement += "; Initial state constraint \n";
                            cout << ("; Initial state constraint \n");
                            in_out_enforcement += create_assertion(create_statement("=", create_sum(in_vars), create_sum(out_vars)));
                        }
                        else
                            in_out_enforcement += create_assertion(create_statement("=", create_sum(in_vars), create_sum(out_vars)));
                    }
                }

                //states vector containing states in receive copy
                states = (cprocess.get_states(process_receive,state_name_receive));
                for(i=0;i<states.size();i++)
                {
                    for(j=1;j<=bound;j++)
                    {
                        stringstream result1;
                        result1 << j;
                        in_out_enforcement += "; constraint of state " + states[i] + "_" + result1.str() + " \n";
                        //cout << ("; constraint of state " + states[i] + "_" + result1.str() + " \n");
                        in_vars = get_in_i_vars(cprocess, process_receive, process_send, state_name_receive, state_name_send, transition_symbol_receive, transition_message_receive, transition_symbol_send, transition_message_send, states[i], j, bound,final_state_receive, final_state_send);
                        out_vars = get_out_i_vars(cprocess, process_receive, process_send, state_name_receive, state_name_send, transition_symbol_receive, transition_message_receive, transition_symbol_send, transition_message_send, states[i], j, bound,final_state_receive, final_state_send);
                        in_out_enforcement += create_assertion(create_statement("<=", create_sum(in_vars), "1"));
                        if((states[i] + "_" + result1.str()) == ((*state_name_receive)[final_state_receive] + "_" + result.str()))
                        {
                            out_vars.push_back("1");
                            in_out_enforcement += "; Final state constraint \n";
                            cout << ("; Final state constraint \n");
                            in_out_enforcement += create_assertion(create_statement("=", create_sum(in_vars), create_sum(out_vars)));
                        }
                        else
                            in_out_enforcement += create_assertion(create_statement("=", create_sum(in_vars), create_sum(out_vars)));
                    }
                }

                in_out_enforcement += "; adding computation order constraint and ensuring connectivity \n";
                cout << ("; adding computation order constraint and ensuring connectivity \n");
                string o_var_in, o_var_out, i_var_in, i_var_out, has_positive_in_flow, one_in_flow_trans_has_smaller_i_var_than_one_out_flow_trans;
    
                //states vector containing states in send copy
                states = (cprocess.get_states(process_send,state_name_send));
                for(i=0;i<states.size();i++)
                {
                    for(j=1;j<=bound;j++)
                    {
                        stringstream result1;
                        result1 << j;
                        in_out_enforcement += "; constraint of state " + states[i] + "_" + result1.str() + " \n";
                        //cout << ("; constraint of state " + states[i] + "_" + result1.str() + " \n");
                        vector<string> all_disjuncts;
                        in_vars = get_in_i_vars(cprocess, process_send, process_receive, state_name_send, state_name_receive, transition_symbol_send, transition_message_send, transition_symbol_receive, transition_message_receive, states[i], j, bound,final_state_send, final_state_receive);
                        out_vars = get_out_i_vars(cprocess, process_send, process_receive, state_name_send, state_name_receive, transition_symbol_send, transition_message_send, transition_symbol_receive, transition_message_receive, states[i], j, bound,final_state_send, final_state_receive);
                        in_flow_sum = create_sum(in_vars);
                        has_positive_in_flow = create_statement(">", in_flow_sum, "0");

                        for(l=0;l<in_vars.size();l++)
                            for(m=0;m<out_vars.size();m++)
                            {
                                if(cprocess.check_left_unique_state(states[i]))
                                {
                                    if(out_vars[m].find("F_$$") != out_vars[m].npos)
                                    {
                                        i_var_in = "i_" + in_vars[l].substr(2, in_vars[l].length());
                                        i_var_out = "i_l_" + out_vars[m].substr(2, out_vars[m].length());
                                        o_var_in = "o_" + in_vars[l].substr(2, in_vars[l].length());
                                        o_var_out = "o_" + out_vars[m].substr(2, out_vars[m].length());
                                    }
                                    else
                                    {
                                        i_var_in = "i_" + in_vars[l].substr(2, in_vars[l].length());
                                        i_var_out = "i_" + out_vars[m].substr(2, out_vars[m].length());
                                        o_var_in = "o_" + in_vars[l].substr(2, in_vars[l].length());
                                        o_var_out = "o_" + out_vars[m].substr(2, out_vars[m].length());
                                    }
                                }
                                else if(cprocess.check_right_unique_state(states[i]))
                                {
                                    if(in_vars[l].find("I_$$") != in_vars[l].npos)
                                    {
                                        i_var_in = "i_r_" + in_vars[l].substr(2, in_vars[l].length());
                                        i_var_out = "i_" + out_vars[m].substr(2, out_vars[m].length());
                                        o_var_in = "o_" + in_vars[l].substr(2, in_vars[l].length());
                                        o_var_out = "o_" + out_vars[m].substr(2, out_vars[m].length());
                                    }
                                    else
                                    {
                                        i_var_in = "i_" + in_vars[l].substr(2, in_vars[l].length());
                                        i_var_out = "i_" + out_vars[m].substr(2, out_vars[m].length());
                                        o_var_in = "o_" + in_vars[l].substr(2, in_vars[l].length());
                                        o_var_out = "o_" + out_vars[m].substr(2, out_vars[m].length());

                                    }
                                }
                                else
                                {
                                    i_var_in = "i_" + in_vars[l].substr(2, in_vars[l].length());
                                    i_var_out = "i_" + out_vars[m].substr(2, out_vars[m].length());
                                    o_var_in = "o_" + in_vars[l].substr(2, in_vars[l].length());
                                    o_var_out = "o_" + out_vars[m].substr(2, out_vars[m].length());
                                }

                                vector<string> conjuncts;
                                conjuncts.push_back(create_statement(">", o_var_in, "0"));
                                conjuncts.push_back(create_statement(">", o_var_out, "0"));
                                conjuncts.push_back(create_statement(">", i_var_out, i_var_in));
                                all_disjuncts.push_back(create_conjunction(conjuncts));
                            }

                        one_in_flow_trans_has_smaller_i_var_than_one_out_flow_trans = create_disjunction(all_disjuncts);
                        in_out_enforcement += create_assertion(create_implication(has_positive_in_flow, one_in_flow_trans_has_smaller_i_var_than_one_out_flow_trans));
                    }
                }

                //states vector containing states in receive copy
                states = (cprocess.get_states(process_receive,state_name_receive));
                for(i=0;i<states.size();i++)
                {
                    for(j=1;j<=bound;j++)
                    {
                        stringstream result1;
                        result1 << j;
                        if(states[i] + "_" + result1.str() != (*state_name_receive)[final_state_receive] + "_" + result.str())
                        {
                            in_out_enforcement += "; constraint of state " + states[i] + "_" + result1.str() + " \n";
                            //cout << ("; constraint of state " + states[i] + "_" + result1.str() + " \n");
                            vector<string> all_disjuncts;
                            in_vars = get_in_i_vars(cprocess, process_receive, process_send, state_name_receive, state_name_send, transition_symbol_receive, transition_message_receive, transition_symbol_send, transition_message_send, states[i], j, bound,final_state_receive, final_state_send);
                            out_vars = get_out_i_vars(cprocess, process_receive, process_send, state_name_receive, state_name_send, transition_symbol_receive, transition_message_receive, transition_symbol_send, transition_message_send, states[i], j, bound,final_state_receive, final_state_send);
                            in_flow_sum = create_sum(in_vars);
                            has_positive_in_flow = create_statement(">", in_flow_sum, "0");

                            for(l=0;l<in_vars.size();l++)
                                for(m=0;m<out_vars.size();m++)
                                {
                                    i_var_in = "i_" + in_vars[l].substr(2, in_vars[l].length());
                                    i_var_out = "i_" + out_vars[m].substr(2, out_vars[m].length());
                                    o_var_in = "o_" + in_vars[l].substr(2, in_vars[l].length());
                                    o_var_out = "o_" + out_vars[m].substr(2, out_vars[m].length());

                                    vector<string> conjuncts;
                                    conjuncts.push_back(create_statement(">", o_var_in, "0"));
                                    conjuncts.push_back(create_statement(">", o_var_out, "0"));
                                    conjuncts.push_back(create_statement(">", i_var_out, i_var_in));
                                    all_disjuncts.push_back(create_conjunction(conjuncts));
                                }

                            one_in_flow_trans_has_smaller_i_var_than_one_out_flow_trans = create_disjunction(all_disjuncts);
                            in_out_enforcement += create_assertion(create_implication(has_positive_in_flow, one_in_flow_trans_has_smaller_i_var_than_one_out_flow_trans));
                        }
                    }
                }
            }

            jump2:
            return in_out_enforcement;
        }

        /*Ensuring that if the occurence varible of a receive transition is greater than 0
        then their exists a send transition on the same message such that its index is greater than that of the receive transition
        and its occurence variable is also greater than 0.
        Finally equating the index variable of the above found send transition with the match variable of the receive transition*/
        string enforcing_receive_transitions_matching(CommunicatingProcess cprocess, int bound, string channel_type)
        {
            string receive_transition_match("");
            string msg, recv_o, recv_m, recv_i, send_i, send_o, receive_msg_occurred, send_matches_receive, send_interim;
            int i, j, l;

            vector<vector<string> > temp;
            vector<string>::iterator it;
            cout << "; enforcing matching of each occuring receive transitions \n";

            /*If channel_type is xml then each receive operation can only receive from a particular channel and is then 
            matched to that send transition which sended to that same channel.
            Note that a send transition at one one time can send to only one particular channel*/
            if(channel_type != "xml")
            {
                for(it=Aut_messages.begin(); it!=Aut_messages.end(); ++it)
                {
                    msg = *it;
                    vector<vector<string> > sends,receives;
                    for(j=1;j<Processes.size();j= j+2)
                    {
                        temp = get_i_var_o_var_m_var_triples_for_msg(cprocess, Processes[j], Process_state_name[j], Process_transition_symbol[j], Process_transition_message[j], Process_channel[j], msg, bound, "dummy", channel_type);
                        receives.insert(receives.end(), temp.begin(), temp. end());
                    }                    
               
                    for(j=0;j<Processes.size();j= j+2)
                    {
                        temp = get_i_var_o_var_pairs_for_send_of_msg(cprocess, Processes[j], Process_state_name[j], Process_transition_symbol[j], Process_transition_message[j], Process_channel[j], msg, bound, "dummy", channel_type);
                        sends.insert(sends.end(), temp.begin(), temp. end());
                    }

                    for(j=0;j<receives.size();j++)
                    {
                        recv_i = receives[j][0];
                        recv_o = receives[j][1];
                        recv_m = receives[j][2];
                        receive_msg_occurred = create_statement(">", recv_o, "0");
                        vector<string> disjuncts;
                        for(l=0;l<sends.size();l++)
                        {
                            if(sends[l].size() == 2)
                            {
                                send_i = sends[l][0];
                                send_o = sends[l][1];
                                vector<string> conjuncts;
                                conjuncts.push_back(create_statement("=", recv_m, send_i));
                                conjuncts.push_back(create_statement(">", send_o, "0"));
                                conjuncts.push_back(create_statement("<", send_i, recv_i));
                                disjuncts.push_back(create_conjunction(conjuncts));
                            }
                            else
                            {
                                send_i = sends[l][0];
                                send_interim = sends[l][1];
                                send_o = sends[l][2];
                                vector<string> conjuncts;
                                conjuncts.push_back(create_statement(">=", recv_m, send_i));
                                conjuncts.push_back(create_statement("<=", recv_m, send_interim));
                                conjuncts.push_back(create_statement(">", send_o, "0"));
                                conjuncts.push_back(create_statement("<", send_interim, recv_i));
                                disjuncts.push_back(create_conjunction(conjuncts));
                            }
                        }
                        send_matches_receive = create_disjunction(disjuncts);
                        receive_transition_match += create_assertion(create_implication(receive_msg_occurred, send_matches_receive));
                    }
                }
            }
            /*If channel_type is process or prefix , i.e. not xml, then a receive transition can receive from any channel but here also a send
            transition at one one time can send to only one particular channel*/
            else
            {
                for(auto it = Channels.begin(); it != Channels.end(); ++it)
                {
                    vector<vector<string> > sends,receives;
                    for(auto it1 = (it->second).begin(); it1 != (it->second).end(); ++it1)
                    {
                        msg = *it1;
                        vector<vector<string> > sends,receives;
                        for(j=1;j<Processes.size();j= j+2)
                        {
                            temp = get_i_var_o_var_m_var_triples_for_msg(cprocess, Processes[j], Process_state_name[j], Process_transition_symbol[j], Process_transition_message[j], Process_channel[j], msg, bound, it->first, channel_type);
                            receives.insert(receives.end(), temp.begin(), temp. end());
                        }                    
                   
                        for(j=0;j<Processes.size();j= j+2)
                        {
                            temp = get_i_var_o_var_pairs_for_send_of_msg(cprocess, Processes[j], Process_state_name[j], Process_transition_symbol[j], Process_transition_message[j], Process_channel[j], msg, bound, it->first, channel_type);
                            sends.insert(sends.end(), temp.begin(), temp. end());
                        }

                        for(j=0;j<receives.size();j++)
                        {
                            recv_i = receives[j][0];
                            recv_o = receives[j][1];
                            recv_m = receives[j][2];
                            receive_msg_occurred = create_statement(">", recv_o, "0");
                            vector<string> disjuncts;
                            for(l=0;l<sends.size();l++)
                            {
                                if(sends[l].size() == 2)
                                {
                                    send_i = sends[l][0];
                                    send_o = sends[l][1];
                                    vector<string> conjuncts;
                                    conjuncts.push_back(create_statement("=", recv_m, send_i));
                                    conjuncts.push_back(create_statement(">", send_o, "0"));
                                    conjuncts.push_back(create_statement("<", send_i, recv_i));
                                    disjuncts.push_back(create_conjunction(conjuncts));
                                }
                                else
                                {
                                    send_i = sends[l][0];
                                    send_interim = sends[l][1];
                                    send_o = sends[l][2];
                                    vector<string> conjuncts;
                                    conjuncts.push_back(create_statement(">=", recv_m, send_i));
                                    conjuncts.push_back(create_statement("<=", recv_m, send_interim));
                                    conjuncts.push_back(create_statement(">", send_o, "0"));
                                    conjuncts.push_back(create_statement("<", send_interim, recv_i));
                                    disjuncts.push_back(create_conjunction(conjuncts));
                                }
                            }
                            send_matches_receive = create_disjunction(disjuncts);
                            receive_transition_match += create_assertion(create_implication(receive_msg_occurred, send_matches_receive));
                        }
                    }
                }
            }

            return receive_transition_match;
        }

        /*For lossy semantics, ensuring that if two receive transitions are receiving from the same channel 
        and have their occurence variable > 0 and the index varible of first is less than the index variable of second, 
        then the send transition matching to first should happen before the send transition matching to second*/
        string enforcing_lossy_computation_order_for_transitions_pair_per_channel(CommunicatingProcess cprocess, int bound, string channel_type)
        {
            string enforcement("");
            vector<vector<string> > temp;
            string msg, both_occurred_and_in_order_1_after_2, m1_occurred_after_m2, if_both_occurred_and_1_after_2_then_m1_occurred_after_m2;
            int i, j, l;
            cout << "; enforcing computation order for transitions pair per channel \n";

            for(auto it = Channels.begin(); it != Channels.end(); ++it)
            {
                vector<vector<string> > rcvs;
                for(j=1;j<Processes.size();j=j+2)
                {
                    for(auto it1 = (it->second).begin(); it1 != (it->second).end(); ++it1)
                    {
                        msg = *it1;
                        temp = get_i_var_o_var_m_var_triples_for_msg(cprocess, Processes[j], Process_state_name[j], Process_transition_symbol[j], Process_transition_message[j], Process_channel[j], msg, bound, it->first, channel_type);
                        rcvs.insert(rcvs.end(), temp.begin(), temp.end());
                    }
                }

                for(j=0;j<rcvs.size();j++)
                {
                    for(l=0;l<rcvs.size();l++)
                    {
                        vector<string> conjuncts;
                        if(rcvs[j][0] != rcvs[l][0])
                        {
                            conjuncts.push_back(create_statement(">", rcvs[j][1], "0"));
                            conjuncts.push_back(create_statement(">", rcvs[l][1], "0"));
                            conjuncts.push_back(create_statement(">", rcvs[j][0], rcvs[l][0]));
                            both_occurred_and_in_order_1_after_2 = create_conjunction(conjuncts);
                            m1_occurred_after_m2 = create_statement(">", rcvs[j][2], rcvs[l][2]);
                            if_both_occurred_and_1_after_2_then_m1_occurred_after_m2 = create_implication(both_occurred_and_in_order_1_after_2, m1_occurred_after_m2);
                            enforcement += create_assertion(if_both_occurred_and_1_after_2_then_m1_occurred_after_m2);
                        }
                    }
                }
            }
            jump:
            return enforcement;
        }

        /*For stuttering semantics, ensuring that if two receive transitions are receiving from the same channel 
        and have their occurence variable > 0 and the index varible of first is less than the index variable of second ,
        then the send transition matching to first should happen before or is equal to the send transition matching to second*/
        string enforcing_stuttering_computation_order_for_transitions_pair_per_channel(CommunicatingProcess cprocess, int bound, string channel_type)
        {
            string enforcement("");
            vector<vector<string> > temp;
            string msg, both_occurred_and_in_order_1_after_2, m1_occurred_after_together_m2, if_both_occurred_and_1_after_2_then_m1_occurred_after_m2;
            int i, j, l;
            cout << "; enforcing computation order for transitions pair per channel \n";

            for(auto it = Channels.begin(); it != Channels.end(); ++it)
            {
                vector<vector<string> > rcvs;
                for(j=1;j<Processes.size();j=j+2)
                {
                    for(auto it1 = (it->second).begin(); it1 != (it->second).end(); ++it1)
                    {
                        msg = *it1;
                        temp = get_i_var_o_var_m_var_triples_for_msg(cprocess, Processes[j], Process_state_name[j], Process_transition_symbol[j], Process_transition_message[j], Process_channel[j], msg, bound, it->first, channel_type);
                        rcvs.insert(rcvs.end(), temp.begin(), temp.end());
                    }
                }

                for(j=0;j<rcvs.size();j++)
                {
                    for(l=0;l<rcvs.size();l++)
                    {
                        vector<string> conjuncts;
                        if(rcvs[j][0] != rcvs[l][0])
                        {
                            conjuncts.push_back(create_statement(">", rcvs[j][1], "0"));
                            conjuncts.push_back(create_statement(">", rcvs[l][1], "0"));
                            conjuncts.push_back(create_statement(">", rcvs[j][0], rcvs[l][0]));
                            both_occurred_and_in_order_1_after_2 = create_conjunction(conjuncts);
                            m1_occurred_after_together_m2 = create_statement(">=", rcvs[j][2], rcvs[l][2]);
                            if_both_occurred_and_1_after_2_then_m1_occurred_after_m2 = create_implication(both_occurred_and_in_order_1_after_2, m1_occurred_after_together_m2);
                            enforcement += create_assertion(if_both_occurred_and_1_after_2_then_m1_occurred_after_m2);
                        }
                    }
                }
            }
            jump:
            return enforcement;
        }

        /*For unordered semantics, ensuring that if two receive transitions are receiving from the same channel 
        and have their occurence variable > 0 and the index varible of first is less than the index variable of second ,
        then the send transition matching to first should not be equal to the send transition matching to second*/
        string enforcing_unordered_computation_order_for_transitions_pair_per_channel(CommunicatingProcess cprocess, int bound, string channel_type)
        {
            string enforcement("");
            vector<vector<string> > temp;
            string msg, both_occurred_and_in_order_1_after_2, m1_not_equal_m2, if_both_occurred_and_1_after_2_then_m1_occurred_after_m2;
            int i, j, l;
            cout << "; enforcing computation order for transitions pair per channel \n";

            for(auto it = Channels.begin(); it != Channels.end(); ++it)
            {
                vector<vector<string> > rcvs;
                for(j=1;j<Processes.size();j=j+2)
                {
                    for(auto it1 = (it->second).begin(); it1 != (it->second).end(); ++it1)
                    {
                        msg = *it1;
                        temp = get_i_var_o_var_m_var_triples_for_msg(cprocess, Processes[j], Process_state_name[j], Process_transition_symbol[j], Process_transition_message[j], Process_channel[j], msg, bound, it->first, channel_type);
                        rcvs.insert(rcvs.end(), temp.begin(), temp.end());
                    }
                }

                for(j=0;j<rcvs.size();j++)
                {
                    for(l=0;l<rcvs.size();l++)
                    {
                        vector<string> conjuncts;
                        if(rcvs[j][0] != rcvs[l][0])
                        {
                            conjuncts.push_back(create_statement(">", rcvs[j][1], "0"));
                            conjuncts.push_back(create_statement(">", rcvs[l][1], "0"));
                            conjuncts.push_back(create_statement(">", rcvs[j][0], rcvs[l][0]));
                            both_occurred_and_in_order_1_after_2 = create_conjunction(conjuncts);
                            m1_not_equal_m2 = create_negate(create_statement("=", rcvs[j][2], rcvs[l][2]));
                            if_both_occurred_and_1_after_2_then_m1_occurred_after_m2 = create_implication(both_occurred_and_in_order_1_after_2, m1_not_equal_m2);
                            enforcement += create_assertion(if_both_occurred_and_1_after_2_then_m1_occurred_after_m2);
                        }
                    }
                }
            }
            jump:
            return enforcement;
        }

        //Creating conjunction of a lists of string variable in accordance to the syntax acceptable by Z3 solver
        string create_conjunction(vector<string> conjuncts)
        {
            if (conjuncts.empty())
                return "true";
            string temp = conjuncts[0];
            conjuncts.erase(conjuncts.begin());
            return create_statement("and", temp, create_conjunction(conjuncts));
        }

        //Creating disjunction of a lists of string variable in accordance to the syntax acceptable by Z3 solver
        string create_disjunction(vector<string> disjuncts)
        {
            string gen_or("");
            int i;
            if(disjuncts.size()==0)
                return "false";
            for(i=0;i<disjuncts.size();i++)
                gen_or += "(or ";
            gen_or += "false ";
            for(i=0;i<disjuncts.size();i++)
                gen_or += disjuncts[i] + " ) ";
            return gen_or;
        }

        //Creating sum of a lists of string variable in accordance to the syntax acceptable by Z3 solver
        string create_sum(vector<string> terms)
        {
            if(terms.size()==0)
                return "0";
            string gen_sum("");
            int i;
            for(i=0;i<terms.size();i++)
                gen_sum += "(+ ";
            gen_sum += "0 ";
            for(i=0;i<terms.size();i++)
                gen_sum += terms[i] + " ) ";
            return gen_sum;
        }

        //Creating distinct statement of a lists of string variable in accordance to the syntax acceptable by Z3 solver
        string create_distinct_statement(vector<string> terms)
        {   
            string distinct("");
            if(terms.size() == 0)
                return "true";

            distinct += "(distinct ";
            int i;
            for(i=0;i<terms.size();i++)
                distinct += (terms[i] + " ");
            distinct += ")";

            return distinct;
        }

        //Creating negation of a statement in accordance to the syntax acceptable by Z3 solver
        string create_negate(string statement)
        {
            return create_statement("not", statement, "");
        }

        //Creating a statement containing implication in accordance to the syntax acceptable by Z3 solver
        string create_implication(string antecedent, string consequent)
        {
            return create_statement("=>", antecedent, consequent);
        }

        //Creating a statement in accordance to the syntax acceptable by Z3 solver
        string create_statement(string cond, string arg1, string arg2)
        {   
            if(arg2.empty())
                return "(" + cond + " " + arg1 + ")";    
            return "(" + cond + " " + arg1 + " " + " " + arg2 +  ")";
        }

        //Creating an assertion in accordance to the syntax acceptable by Z3 solver
        string create_assertion(string statement)
        {
            num_asserts += 1;
            return "(assert " + statement + " ) \n";
        }
};