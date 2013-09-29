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

#include "constraints_generation.hpp"

/*Main class containing declaration of the object of the Constraint class.
Responsible for calls to all the other class which are validated by the call to constructor*/
class Engine
{
    std::unordered_map<string, vector<string> > bad;
    int bound;
    string semantics;
    string file_name;
    string channel_type;
    time_t z3_time;
    float total_time;
    char buffer[128];
    string result, output;
    string protocol_name, protocol_name_1, bad_name, sem_name;

    public:
        /*Constructor of the class Engine. & {\\bf Sem}
        Generates automata from xml file and presburger formula type input to be solved by smt solver 
        by creating an object of class Constraint and then also generates: 
        1: output from smt solver Z3
        2: output to GUI
        3: a latex file containing the results in a table format*/
        Engine(char *settings_file, string type1)
        {
            get_information(settings_file);
            cout << "----------\n----------\n";
            Constraint Presburger_formula(file_name.c_str(), bad, bound, channel_type, semantics);
            is_satisfiable(Presburger_formula.get_query());
            assigning_specification(Presburger_formula);
            print(Presburger_formula);
            cout << "----------\n----------\n";
            if(type1 != "false")
            {
                filter_data(type1);
                output_tex(Presburger_formula);
            }
        }

        //Checks whether the provided input in the Settings file is valid or not
        void get_information(char *settings_file)
        {
            string temp_string;
            ifstream setting_file;
            setting_file.open(settings_file);
            if(setting_file)
            {
                while(getline(setting_file,temp_string,' '))
                    {
                        if( temp_string.substr(0,1) == "#")
                        {
                            getline(setting_file,temp_string,'\n');
                            continue;
                        }
                        else if(temp_string == "file")
                        {
                            getline(setting_file,temp_string,'\n');
                            file_name = temp_string;
                            if(temp_string == "")
                            {
                                cout<<"File path not entered!"<<endl<<"Exiting"<<endl;
                                exit(0);
                            }
                            continue;
                        }
                        else if(temp_string == "bad")
                        {
                            getline(setting_file,temp_string);
                            if(temp_string == "")
                            {
                                cout<<"Bad Role not entered!"<<endl<<"Exiting"<<endl;
                                exit(0);
                            }
                            string role;
                            stringstream iis;
                            iis << temp_string;
                            bool flag = false;
                            while(getline(iis,temp_string,' '))
                            {
                                if(flag == false)
                                {
                                    role = temp_string;;
                                    flag = true;
                                }
                                else if(flag == true)
                                {
                                    if(temp_string == "")
                                    {
                                            cout<<"Bad state not entered!"<<endl<<"Exiting"<<endl;
                                            exit(0);
                                    }
                                    (bad[role]).push_back(temp_string);
                                }
                            }
                            continue;
                        }
                        else if(temp_string == "semantics")
                        {
                            getline(setting_file,temp_string,'\n');
                            if(temp_string == "")
                            {
                                cout<<"Semantics not entered!"<<endl<<"Exiting"<<endl;
                                exit(0);
                            }
                            semantics = temp_string;
                            std::transform(semantics.begin(), semantics.end(), semantics.begin(), ::tolower);
                            if(semantics != "lossy" && semantics != "stuttering" && semantics != "unordered")
                            {
                                cout<<"Invalid Semantics entered!"<<endl<<"Exiting"<<endl;
                                exit(0);
                            }
                            continue;
                        }
                        else if(temp_string == "channel_type")
                        {
                            getline(setting_file,temp_string,'\n');
                            if(temp_string == "")
                            {
                                cout<<"Channel type not entered!"<<endl<<"Exiting"<<endl;
                                exit(0);
                            }
                            channel_type = temp_string;
                            if(channel_type != "prefix" && channel_type != "process" && channel_type != "xml")
                            {
                                cout<<endl<<"Invalid channel_type value!"<<endl<<"Exiting"<<endl;
                                exit(0);
                            }
                            continue;
                        }
                        else if(temp_string == "bound")
                        {
                            getline(setting_file,temp_string,'\n');
                            if(temp_string == "")
                            {
                                cout<<"Bound not entered!"<<endl<<"Exiting"<<endl;
                                exit(0);
                            }
                            bound = atoi(temp_string.c_str());
                            continue;
                        }
                    }
            }
            else
            {
                cout << "Settings File not found" << endl << endl;
                exit(0);
            }
        }

        //Calls Z3 solver to generate output and then save the same in a file
        void is_satisfiable(string query)
        {
            struct passwd *pw = getpwuid(getuid());
            const char *homedir = pw->pw_dir;
            query += "(check-sat)";
            query += "(get-model)";
            string input_path = homedir+(string)"/verifier_result/smt_solver_input_presburger_formula.txt";
            ofstream myfile;
            myfile.open(input_path.c_str());
            myfile << query;
            myfile.close();

            z3_time = time(0);
            string z3_command = "z3 -smt2 " + input_path;
            FILE* pipe = popen(z3_command.c_str(),"r");
            if(!pipe) 
                cout << "\n ERROR";

            int i=0;
            result = "";
            output = "";

            while(!feof(pipe)) 
            {
                if(fgets(buffer, 128, pipe) != NULL)
                    output += buffer;
                if(i == 0)
                    result = buffer;
                i++;
            }
            pclose(pipe);

            z3_time=time(0) - z3_time;

            ofstream temp_file;
            string output_path = homedir+(string)"/verifier_result/smt_solver_output.txt";
            temp_file.open(output_path.c_str());
            temp_file << output;
            temp_file.close();
        }

        //Function to assign protocol name, bad state value and semantics name into a varible
        void assigning_specification(Constraint Presburger_formula)
        {
            string tem("");
            stringstream ss;
            ss << file_name;

            //For protocol name entry into the table
            while(getline(ss,tem,'/'))
            {}

            protocol_name = tem.substr(0,tem.length()-4);
            protocol_name_1 = protocol_name;

            int s;
            while((s = protocol_name_1.find("_")) != protocol_name_1.npos)
            {
                protocol_name_1.replace(s, 1, "{\\textunderscore}");
            }

            //For bad state name and corresponding role  entry into the table
            auto it = bad.begin();
            bad_name += "\\shortstack{";
            while(it != bad.end())
            {
                bad_name += it->first;
                for(int i=0; i<(it->second).size(); i++)
                {
                    bad_name += " ";
                    bad_name += (it->second)[i];
                }
                ++it;
                if(it != bad.end())
                    bad_name += " \\\\ ";
            }
            bad_name += "}";

            //Sematic value entry into the table
            if(semantics == "lossy")
                sem_name = "LCS";
            else if(semantics == "stuttering")
                sem_name = "SLCS";
            else
                sem_name = "UCS";

        }

        //Function to print details of generated automata, time statistics and the final result to the UI
        void print(Constraint Presburger_formula)
        {
            stringstream ss, temp, temp1, temp2, temp3, temp4;
            total_time = z3_time + ((float)(Presburger_formula.get_constraint_automata_generation_time())/CLOCKS_PER_SEC);
            double cc_time = total_time - z3_time;
            string bad_name_1 = bad_name;
            int s;

            while((s = bad_name_1.find("\\\\")) != bad_name_1.npos)
            {
                bad_name_1.replace(s, 2, "--");
            }

            temp << bound;
            temp1 << z3_time;
            temp2 << total_time;
            temp3 << Presburger_formula.get_number_of_assertions();
            temp4 << showDecimals(cc_time, 2);

            cout << "----------AUTOMATA STATISTICS----------\n";
            cout << "Total Number of non-unique transitions: " << global_i_vars.size() << "\n";
            cout << "Total Number of unique transitions: " << Presburger_formula.get_unique_no()*bound << "\n";
            cout << "Total Number of states: " << Presburger_formula.get_no_states()*bound << "\n";
            cout << "Number of Assertions : " << Presburger_formula.get_number_of_assertions() << "\n";

            cout << "----------TIME STATISTICS----------\n";
            cout << "Automata and Constraint genertaion time for generating Presburger Formula: " << ((float)(Presburger_formula.get_constraint_automata_generation_time())/CLOCKS_PER_SEC) << " seconds \n";
            cout << "SMT Solver time for generating output by Presburger_formula theorem Prover: " << z3_time << " seconds \n";
            cout << "Total time elapsed: " << total_time << " seconds \n";

            cout << "----------RESULT----------\n";

            if (result.find("unsat") != result.npos)
                cout << ("Protocol_name = " + protocol_name + "\n" + "Bad_state_name = " + bad_name_1.substr(12, bad_name_1.length()-13) + "\n" + "Semantics = " + sem_name + "\n" + "Channel_Type = " + "By " + channel_type + "\n" + "Constraint Generation Time = " + temp4.str() + " sec" + "\n" +  "SMT Time = " + temp1.str() + " sec" + "\n" +  "Total Time = " + temp2.str() + " sec" + "\n" +  "Assertions = " + temp3.str() + "\n" + "Bound = " + temp.str() + "\n" +  "Result = " + "S(unsat)" ) << "\n";
            else
                cout << ("Protocol_name = " + protocol_name + "\n" + "Bad_state_name = " + bad_name_1.substr(12, bad_name_1.length()-13) + "\n" + "Semantics = " + sem_name + "\n" + "Channel_Type = " + "By " +  channel_type + "\n" + "Constraint Generation Time = " + temp4.str() + " sec" + "\n" +  "SMT Time = " + temp1.str() + " sec" + "\n" +  "Total Time = " + temp2.str() + " sec" + "\n" +  "Assertions = " + temp3.str() + "\n" + "Bound = " + temp.str() + "\n" +  "Result = " + "U(sat)" ) << "\n";

            if (result.find("unsat") != result.npos)
                cout << "Thus, the bad State is not reachable for " << semantics << " semantics within the given bound : " << bound << endl;
            else
                cout << "Thus, the bad State is reachable for " << semantics << " semantics within the given bound : " << bound << endl;
                
        }

        //Re creates the tex file containing data of results removing all the table entries which were present before
        void filter_data(string type)
        {
            if(type == "new")
            {
                string input("");
                input += "\\begin{center} \n";
                input += "\\small{ \n";
                input += "\\begin{tabular}{| l | l | l | l | l | l | l | l | l | l |} \n";
                input += "\\hline \n";
                input += "\\hline \n";
                input += "{\\bf P} & {\\bf Bad} & {\\bf Sem} & {\\bf Channel} & {\\bf \\shortstack{Const. \\\\ gen.}} & {\\bf SMT} & {\\bf Total} & {\\bf Assert} & {\\bf Ph.} & {\\bf Res} \\\\  \n";
                input += "\\hline \n";
                input += "\\hline \n";
                input += "%content% \n";
                input += "\\hline \n";
                input += "\\end{tabular}} \n";
                input += "\\end{center} \n";

                ofstream myfile;
                struct passwd *pw = getpwuid(getuid());
                const char *homedir = pw->pw_dir;
                string tex_path =  homedir+(string)"/verifier_result/Result/data.tex";
                myfile.open(tex_path.c_str());
                myfile << input;
                myfile.close();
            }
        }

        //Return a decimal value by rounding it of to two places
        double showDecimals(const double& x, const int& numDecimals)
        {
            int y=x;
            double z=x-y;
            double m=pow(10,numDecimals);
            double q=z*m;
            double r=round(q);

            return static_cast<double>(y)+(1.0/m)*r;
        }

        //Output the result obtained to a tex file and rebuild the pdf file containing this new entry
        void output_tex(Constraint Presburger_formula)
        {
            string data(""), content("");
            stringstream ss, temp, temp1, temp2, temp3, temp4;
            double cc_time = total_time - z3_time;

            temp << bound;
            temp1 << z3_time;
            temp2 << total_time;
            temp3 << Presburger_formula.get_number_of_assertions();
            temp4 << showDecimals(cc_time, 2);

            //Table entry generated by the obtained results
            if (result.find("unsat") != result.npos)
                data += protocol_name_1 + " & " + bad_name + " & " + sem_name + " & " + channel_type + " & " + temp4.str() + " sec & " + temp1.str() + " sec & " + temp2.str() + " sec & " + temp3.str() + " & " + temp.str() + " & S(unsat) \\\\ \\hline";
            else
                data += protocol_name_1 + " & " + bad_name + " & " + sem_name + " & " + channel_type + " & " + temp4.str() + " sec & " + temp1.str() + " sec & " + temp2.str() + " sec & " + temp3.str() + " & " + temp.str() + " & U(sat) \\\\ \\hline";


            //Stacking above entry with the rest of the entries in the tex file
            
            struct passwd *pw = getpwuid(getuid());
            const char *homedir = pw->pw_dir;
            string tex_path = homedir+(string)"/verifier_result/Result/data.tex";
            fstream fi(tex_path.c_str(), ios::out | ios ::in);
            if(!fi)
            {
                filter_data("new");
                fi.open(tex_path.c_str(), ios::out | ios ::in);
            }

            ofstream fi1("temp.txt");
            getline(fi, content);
            while(content.substr(0,9) != "%content%")
            {
                fi1 << content;
                fi1 << "\n";
                getline(fi,content);
            }

            fi1 << "%content%\n";
            fi1 << data << "\n";

            while(getline(fi,content))
            {
                fi1 << content;
                fi1 << "\n";    
            }
            remove(tex_path.c_str());
            rename("temp.txt",tex_path.c_str());

            //Creating latex pdf containing result
            string result_path = homedir + (string)"/verifier_result/Result";
            int k = chdir(result_path.c_str());
            FILE* pipe1 = popen("pdflatex result.tex > /dev/null","w");
            if(!pipe1)
                cout << "\n ERROR";
            int l = chdir("../../");
        }
};

//Main function creating an object of class Engine and thus calling its constructor which further validates other class
int main(int argv, char *argc[])
{
    if(argv > 2)
    {
        if((argv == 3) && argc[2][0] == 'n' && argc[2][1]=='e' && argc[2][2]=='w' && sizeof(argc[3])==4)
            Engine verifier(argc[1], "new");
        else if(argv == 4 || (argc[2][0] == 'o' && argc[2][1]=='l' && argc[2][2]=='d' && sizeof(argc[3])==4))
            Engine verifier(argc[1], "old");
        else
        {
            cout << "Wrong argument passed during execution !" << endl;
            exit(0);
        }
    }
    else if(argv ==2)
    {
        Engine verifier(argc[1],"false");
    }
    else if (argv==1)
    {
        char settings_file[100];
        cout << "Please enter the path to the Settings File : "<<endl;
        cin >> settings_file;
        Engine verifier(settings_file, "false");
    }
    else
    {
        cout << "Wrong argument passed during execution !" << endl;
        exit(0);
    }
}
