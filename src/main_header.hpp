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

#include<iostream>
#include "../Includes/pugixml/src/pugixml.hpp"
#include <lemon/list_graph.h>

#include<stack>
#include<string.h>
#include<fstream>
#include<sstream>
#include<vector>
#include<memory>
#include<unordered_map>
#include<unordered_set>
#include<sys/time.h>
#include<time.h>
#include<pwd.h>

using namespace std;
using namespace pugi;
using namespace lemon;

typedef ListDigraph Graph;
typedef ListDigraph::NodeMap<int> Node_valuess;
typedef ListDigraph::NodeMap<string> Node_namess;
typedef ListDigraph::ArcMap<string> Arc_valuess;
typedef ListDigraph::ArcMap<string> Channel_valuess;
typedef std::shared_ptr<Graph> Process_pointer;
typedef std::shared_ptr<Node_valuess> Nvalue_pointer;
typedef std::shared_ptr<Node_namess> Nname_pointer;
typedef std::shared_ptr<Arc_valuess> Avalues_pointer;
typedef std::shared_ptr<Channel_valuess> Cvalue_pointer;
vector<string> global_i_vars;
