using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;
using System.Diagnostics;
//using ILOG.Concert;
//using ILOG.CPLEX;
using System.Data.SqlClient;
using Gurobi;
using System.Threading.Tasks;
using IMP_core_pipage;
using System.Threading;

namespace IMP_core_pipage
{
    class Program
    {
        static int N, N2, E, BIGM, trial_limit, k_init, seed, solution_method, SAA_M, SAA_N1, SAA_T, SAA_N2, SAA_N3, total_network_depth, Cplex_seconds, k_max, run_pipage, run_CELF, run_LR, run_MIP, run_LATIN, run_reduction, run_MEM, theoption, runLT, runTIPTOP, LR_NG_Cuts, no_of_LR_iter;
        static int symmetric_network, save_model, save_log2, mip_model_version, max_network_depth, mip_with_cuts, networkID, is_BUDGETED, counter_prob, counter_prob2;
        static uint m_w, m_z;
        static int[] no_of_active_set, indegree, outdegree, SAA_total_network_depth, SAA_max_network_depth, memory_sample;
        static long[] node_score;
        static double prop_prob, SA_1_hat_obj, SA_3_obj, param_epgap, BUDGET, R1_avg, R1_var, R1_std, T_avg, T_var, T_std, T2_avg, T2_var, T2_std, prob_scaler, pipage_objective_LP, pipage_objective_IP, pipage_T, tiptop_eps, tiptop_rho;
        static double CELF_z, CELF_t, z_pipageInf, z_LRUB, z_LRLB, zLRinf, t_LR, fixed_probability, mem_limit;
        static double[] CELF_z_arr, CELF_t_arr, y_obj;
        static int[,] arcs_int;
        static int[] node_index;
        static int[,] arcs_intID, recorded_RR;
        static bool[,] x_exist;
        static int[,,] network_depth;
        static string filename, pipage_solution, CELF_solution, LR_1_solution, pipage_count, solution_LR;
        static string[] file_names, CELF_sol_arr;
        static string[,,] SAA_neigh, SAA_pred, SAA_tree, SAA_fwd_tree;
        static double[] avg_no_AS, node_threshold, SA_1_obj, SA_1_test_obj, SA_2_obj, recruitment_cost, T_LB, T2_LB, y_i, LP_duals;
        static double[,] influence_prob, SAA_1_prb, SAA_2_prb, SAA_3_prob, Beta_ir, x_ir;
        static float[,] SAA_float;
        static double[,,] SAA_prob, SAA_2_prob;
        static List<int> my_node_set, node_set, init_set, CA_set, active_set, NA_set, selected_set, result_set, SAA_current_list, selected_set2;
        static List<double> arc_weight, arc_distance, accumulated_influence, weight_set;
        static List<string> neigh_set, arc_set, arcID_set, pred_set, neigh_edge_set;
        static List<List<int>> neigh_list, pred_list, Tiptop_pred_list, hypernodes;
        static List<List<int>> neigh_edge_list;
        static List<List<int>> SAA_list, SAA_pipage_list, SAA_LR_list;
        static List<List<double>> SAA_3_prob_dbl, Tiptop_w_list;
        static List<List<List<int>>> SAA_neigh_list, SAA_pred_list, SAA_tree_list, SAA_fwd_tree_list;
        static StreamWriter swvar, swvar2, swvar_summary;
        //static Cplex cplex_model;
        //static ILPMatrix lp_model;
        static Stopwatch sw;
        static TimeSpan sw_elapsed;
        static StreamWriter swtemp2;
        static List<ReadData> unique_arcs;
        static List<ArcsUInt16Weighted> only_arcs;
        static int myoption;

        static void Main(string[] args)
        {
            //swvar_summary=new StreamWriter("results.txt");
            sw = new Stopwatch();

            file_names = new string[10] { "arcs2000", "phy-500", "phy-1k", "phy-2k", "phy-5k", "phy-10k", "phy-20k", "phy-50k", "phy-100k", "phy-200k" };
            //file_names = new string[7] { "run_1K", "run_2K", "run_5K", "run_10K", "run_20K", "run_50K", "run_100K" };
            string[] file_names2 = new string[10] { "GRZ-n1000-k4-b0.3-d1-50-g0-i1", "GRZ-n1000-k4-b0.3-d1-50-g0-i2", "GRZ-n1000-k4-b0.3-d1-50-g0-i3", "GRZ-n1000-k4-b0.3-d1-50-g0-i4", "GRZ-n1000-k4-b0.3-d1-50-g0-i5", "GRZ-n2500-k16-b0.3-d1-50-g0-i1", "GRZ-n2500-k16-b0.3-d1-50-g0-i2", "GRZ-n2500-k16-b0.3-d1-50-g0-i3", "GRZ-n2500-k16-b0.3-d1-50-g0-i4", "GRZ-n2500-k16-b0.3-d1-50-g0-i5" };
            string[] file_names3 = new string[5] { "Email-Enron.im", "phy.im", "p2p-Gnutella04.im", "CollegeMsg.im", "Slashdot0902.txt" };

            int[] SAA_N1_arr = new int[16] { 5, 10, 15, 20, 25, 30, 40, 50, 60, 70, 80, 90, 100, 125, 150, 200 };
            double[] param_epgap_arr = new double[10] { 0.000000, 0.000000, 0.000000, 0.001, 0.003, 0.005, 0.006, 0.007, 0.008, 0.009, };
            int[] fixed_k = new int[7] { 2, 3, 4, 5, 10, 15, 25 };
            int[] fixed_N1 = new int[4] { 30, 200, 300, 500 };
            double[] fixed_probs = new double[2] { 0.01, 0.05 };
            //swvar = new StreamWriter("log-degreecentrality.txt");
            SAA_M = 1;
            SAA_N1 = 1;
            SAA_N2 = 50; 
            SAA_N3 = 50;
            SAA_T = 1;
            prob_scaler = 1;
            //BUDGET = 10;
            Cplex_seconds = 7200;
            myoption = 1; /// use for tests
            is_BUDGETED = 0;
            run_pipage = 0;
            run_CELF = 0;
            run_MIP = 1;
            run_LR = 0;
            LR_NG_Cuts = 0;
            run_LATIN = 0;
            run_reduction = 0;
            runLT = 0;
            runTIPTOP = 0; tiptop_eps = 0.1; tiptop_rho = 0.1;
            run_MEM = 0; mem_limit = 60;
            int file_index_last = file_names.Length;
            file_index_last = 5;
            k_max = 7;

            for (int file_index = 0; file_index < file_index_last; file_index++)
            {
                //file_index =6;
                //SAA_N1 = fixed_N1[file_index];
                filename = file_names3[file_index];
                //filename = file_names[file_index];
                //fixed_probability = fixed_probs[file_index];

                //CELF_main();
                for (int j = 0; j < 1; j++) //jmax=10
                {
                    fixed_probability = 0.99999;
                    //param_epgap = param_epgap_arr[j];

                    //SAA_N1 = fixed_N1[j];
                    initialize_sinan();
                    //initialize();
                    for (int k = 0; k < k_max; k = k + 1) //kmax=5
                    {
                        //BUDGET = 5 + (k-1) *5;
                        k_init = fixed_k[k];
                        k_init = 100;
                        swvar = new StreamWriter("log-" + filename + "_" + k + ".txt");

                        //swvar.Close();
                        swvar2 = new StreamWriter("log2-" + filename + "_" + k + ".txt");
                        BUDGET = k_init;
                        trial_limit = SAA_N1;

                        System.Console.WriteLine("Finished Initialization");

                        System.Console.WriteLine("Iteration K:" + k + "  data: " + filename + " R:" + SAA_N1 + " BUDGET:" + BUDGET + " p:" + fixed_probability);
                        //swvar.WriteLine("Iteration K:" + i + "  data: " + filename + " R:" + k);
                        swvar.Write("Iteration K:" + k + "  data: " + filename + " R:" + SAA_N1 + " BUDGET:" + BUDGET);


                        sw.Start();
                        //SAA();

                        //only_evaluate_influence();
                        if (runTIPTOP == 1)
                        {
                            initialize_neighbourhood_fast_Tiptop();
                            mip_TIPTOP();
                        }

                        else
                            SAA_linderoth();



                        swvar.WriteLine(" , Duration : " + sw_elapsed);


                        sw.Reset();
                        finish();

                        swvar.Close(); swvar2.Close();
                    }

                }

                System.Console.WriteLine("File " + filename + " finished");
            }
        }

        public static void initialize()   // this is obsolete -> using initialize_sinan
        {
            symmetric_network = 0; // 0-> directed network, 1-> undirected network
            int arc_weights_ON = 0;
            int header_row = 0;
            int fix_prob = 1;

            m_w = 521288629;
            m_z = 362436069;
            SetSeedFromSystemTime();

            // read raw data from file
            // Please correct this location for your text file

            string path;
            //path=@"C:\Users\Evren\Downloads\inst\phy.im";
            //path = @"C:\Users\Evren\Downloads\inst\Email-Enron.im";
            //path=@"D:\zz_doktora\ourpapers\2017\IMP-Linear\dataset\facebook_combined_w20p.txt";
            //string[] lines = System.IO.File.ReadAllLines(@"d:\Influence-marketing\Code\influencer-1\" + filename + ".txt");
            //path=@"C:\cygwin64\home\Evren\IMM\" + filename + "\\graph_ic.inf";
            //path = @"C:\Users\Evren\Downloads\inst\p2p-Gnutella04.im";
            //path=(@"C:\Users\Evren\Downloads\inst\CollegeMsg.im");
            //path = (@"D:\Influence-marketing\Code\influencer-1\sample-data-40.txt");
            //string[] lines = System.IO.File.ReadAllLines(@"D:\zz_doktora\ourpapers\2017\IMP-Linear\dataset\ruthmaier_socnet\" + filename + ".txt");
            //string[] lines = System.IO.File.ReadAllLines(@"D:\zz_doktora\ourpapers\2017\IMP-Linear\dataset\banabak.txt");
            //string[] lines = System.IO.File.ReadAllLines(@"D:\zz_doktora\ourpapers\2017\IMP-Linear\dataset\p2p-Gnutella04w20p.txt");
            path = @"D:\Influence-marketing\Code\influencer-1\sample-data-4w.txt";
            //string[] lines = System.IO.File.ReadAllLines(@"D:\zz_doktora\ourpapers\2017\IMP-Linear\dataset\Email-Enron_unw.txt");
            string[] lines = System.IO.File.ReadAllLines(path);

            string[] lines_arr = lines[0].Split(' ');
            System.Console.WriteLine("Finished Reading");
            int number_of_rows = lines.Length;
            arc_set = new List<string>();
            arcID_set = new List<string>();
            node_set = new List<int>();
            my_node_set = new List<int>();
            weight_set = new List<double>();
            string current_arc = null;
            string temp_arc = null;
            double single_arc_weight = 0;
            int skip = 4;
            for (int i = 0 + skip; i < number_of_rows; i++)
            {
                if (i % 50000 == 1)
                    System.Console.WriteLine("read:" + i);
                current_arc = lines[i + header_row];
                if (current_arc != null)
                {
                    string[] nodes_string_arr = current_arc.Split('\t');
                    temp_arc = nodes_string_arr[0] + "," + nodes_string_arr[1];
                    if (!arc_set.Contains(temp_arc))
                    {
                        arc_set.Add(temp_arc);

                        if (arc_weights_ON == 1)
                        {
                            single_arc_weight = (Convert.ToDouble(nodes_string_arr[2]) * prob_scaler);
                        }
                        else
                        {
                            if (fix_prob == 1)
                                single_arc_weight = fixed_probability;
                            else
                                single_arc_weight = GetUniform() * prob_scaler;
                        }
                        weight_set.Add(single_arc_weight);
                        int the_node = Convert.ToUInt16(nodes_string_arr[0]);
                        if (!my_node_set.Contains(the_node))
                            my_node_set.Add(the_node);
                        if (!node_set.Contains(the_node))
                            node_set.Add(the_node);
                        the_node = Convert.ToUInt16(nodes_string_arr[1]);
                        if (!node_set.Contains(the_node))
                            node_set.Add(the_node);

                    }
                    else
                    {
                        int the_index = arc_set.IndexOf(temp_arc);
                        weight_set[the_index] = weight_set[the_index] + fixed_probability;
                    }

                }
            }
            //var readData = File.ReadLines(path).Skip(4).Select(a => {
            //    string[] nodes_string_arr = a.Split(' ');
            //    string temparc = nodes_string_arr[0] + "," + nodes_string_arr[1];
            //    return temparc;
            //}).AsParallel().ToList();
            //.GroupBy(a => a).Select(a => new { Key = a, Count = a.Count() }).AsParallel().ToList();

            N = node_set.Count;
            //double max = weight_set.Max();
            N2 = my_node_set.Count;
            result_set = new List<int>();


            // ---- PARAMETERS
            BIGM = 10000000;
            indegree = new int[N];
            outdegree = new int[N];

            if (symmetric_network == 0)
            { E = arc_set.Count; }
            else
            { E = arc_set.Count * 2; }

            System.Console.WriteLine("Created the network with " + N + " nodes, " + N2 + " controlled nodes and " + E + " arcs");
            arcs_int = new int[E, 2];
            arcs_intID = new int[E, 2];


            //Dij = new int[N, N];
            arc_distance = new List<double>();
            int arc_head;
            int arc_tail;
            string[] arc_arr;

            for (int i = 0; i < N; i++)
            {
                indegree[i] = 0;
                outdegree[i] = 0;
            }

            int head_loc, tail_loc;
            temp_arc = "";
            for (int i = 0; i < E; i++)
            {
                if (arc_weights_ON == 0)
                {
                    if (weight_set[i] > fixed_probability)
                    {
                        weight_set[i] = 1 - Math.Pow((1 - fixed_probability), (weight_set[i] / fixed_probability));
                    }
                }
                arc_arr = arc_set[i].Split(new char[] { ',' });
                arc_head = Convert.ToUInt16(arc_arr[0]);     // ilk node 0 ise böyle, yoksa -1;
                arc_tail = Convert.ToUInt16(arc_arr[1]);

                //                arcs_int[i, 0] = arc_head;
                //                arcs_int[i, 1] = arc_tail;
                head_loc = node_set.IndexOf(arc_head);
                tail_loc = node_set.IndexOf(arc_tail);
                arcs_intID[i, 0] = head_loc;
                arcs_intID[i, 1] = tail_loc;
                indegree[tail_loc]++;
                outdegree[head_loc]++;
                temp_arc = head_loc.ToString() + "," + tail_loc.ToString();
                arcID_set.Add(temp_arc);
            }

            if (symmetric_network == 1)
                for (int i = 0; i < arc_set.Count; i++)
                {
                    arc_arr = arc_set[i].Split(new char[] { ',' });
                    arc_head = Convert.ToUInt16(arc_arr[1]);
                    arc_tail = Convert.ToUInt16(arc_arr[0]);
                    arcs_int[i + E / 2, 0] = arc_head;
                    arcs_int[i + E / 2, 1] = arc_tail;
                    indegree[arc_tail]++;
                    outdegree[arc_head]++;
                }

            //double random_weight = 0;
            //if (arc_weights_ON != 1)
            //{
            //    for (int i = 0; i < arc_set.Count; i++)
            //    {
            //        random_weight = GetUniform() * prob_scaler;
            //        weight_set[i] = random_weight;
            //    }
            //}


            //y_obj = new double[N];      // reduced modeldeki y katsayıları
            recruitment_cost = new double[N];
            //int budget_low = 1;
            //int budget_max = 100;

            if (is_BUDGETED == 1)
            {
                string[] lines_budget = System.IO.File.ReadAllLines(@"d:\Influence-marketing\Code\influencer-1\budget-10k.txt");
                for (int i = 0; i < N; i++)
                {
                    recruitment_cost[i] = System.Convert.ToDouble(lines_budget[i]);
                    //recruitment_cost[i] = r.Next(1, (int)BUDGET) / (BUDGET);
                    //recruitment_cost[i] = i / 10 + 1;
                }
                //recruitment_cost[0] = 1; recruitment_cost[1] = 3; recruitment_cost[2] = 2; recruitment_cost[3] = 5; recruitment_cost[4] = 1; recruitment_cost[5] = 2; recruitment_cost[6] = 4; recruitment_cost[7] = 6; recruitment_cost[8] = 3; recruitment_cost[9] = 5; recruitment_cost[10] = 3; recruitment_cost[11] = 2; recruitment_cost[12] = 4; recruitment_cost[13] = 5; recruitment_cost[14] = 7; recruitment_cost[15] = 6; recruitment_cost[16] = 5; recruitment_cost[17] = 6; recruitment_cost[18] = 4; recruitment_cost[19] = 5; recruitment_cost[20] = 6; recruitment_cost[21] = 5; recruitment_cost[22] = 4;
            }
            else
            {
                for (int i = 0; i < N; i++)
                {
                    //recruitment_cost[i] = System.Convert.ToDouble(lines_budget[i]);
                    recruitment_cost[i] = 1;
                    //recruitment_cost[i] = i / 10 + 1;
                }
                BUDGET = k_init;

            }
            initialize_neighbourhood();           // Arrange the neighbourhood sets
            System.Console.WriteLine("Finished Initialization");
            //test();

        }

        //public static void identify_users_to_be_deleted()
        //{
        //    SqlConnection conn = new SqlConnection(constr);
        //    conn.Open();
        //    SqlCommand command = conn.CreateCommand();

        //    string sqltext = "UPDATE Users set IsToBeDeleted=1 where userID IN (select userID from usersessionhistories where datediff(d, getdate(), lastlogindate)>=181)";
        //            command.CommandText = sqltext;
        //            command.ExecuteNonQuery();
        //}

        //public static void delete_users()
        //{
        //    SqlConnection conn = new SqlConnection(constr);
        //    conn.Open();
        //    SqlCommand command = conn.CreateCommand();

        //    command.CommandText = "select userID from users where IsToBeDeleted=1";
        //    SqlDataReader reader = command.ExecuteReader();
        //    List<int> userIDstobedeleted = new List<int>();
        //    do {
        //        userIDstobedeleted.Add(Convert.ToUInt16(reader["ID"]));
        //    }
        //    while (reader.Read());
        //    reader.Close();

            
        //}


        public static void initialize_sinan()   // read data, create nodes/arcs/B/c_i
        {
            symmetric_network = 0; // 0-> directed network, 1-> undirected network
            int arc_weights_ON = 0;
            int header_row = 0;
            int fix_prob = 0;

            m_w = 521288629;
            m_z = 362436069;
            BIGM = 1000000;
            //SetSeedFromSystemTime();

            // read raw data from file
            // Please correct this location for your text file

            string path;
            //path = @"C:\Users\Evren\Downloads\inst\Email-Enron.im"; // "Email-Enron.im","phy.im","p2p-Gnutella04.im","CollegeMsg.im","Slashdot0902.txt"
            //path=@"C:\Users\Evren\Downloads\inst\phy.im";
            //path = @"C:\Users\Evren\Downloads\inst\p2p-Gnutella04.im";
            //path = @"C:\Users\Evren\Downloads\inst\CollegeMsg.im";
            //path = @"C:\Users\Evren\Downloads\inst\Slashdot0902.txt";
            path = @"C:\Users\Evren\Downloads\inst\" + filename;
            path = @"D:\Influence-marketing\Code\influencer-1\weighted_ic\" + filename+".txt";
            path = @"C:\data\CollegeMsg.im";
            path = @"C:\data\SSM_influence1.txt";
            //path=@"D:\zz_doktora\ourpapers\2017\IMP-Linear\dataset\facebook_combined.txt";
            //path = @"D:\Influence-marketing\Code\influencer-1\sample-data-4w.txt";
            //path = (@"D:\Influence-marketing\Code\influencer-1\sample-data-40blank.txt");
            //path = (@"D:\Influence-marketing\Code\influencer-1\sample-data-20.txt");

            //string[] lines = System.IO.File.ReadAllLines(@"d:\Influence-marketing\Code\influencer-1\" + filename + ".txt");
            //string[] lines = System.IO.File.ReadAllLines(@"C:\cygwin64\home\Evren\IMM\" + filename + "\\graph_ic.inf");
            //string[] lines = System.IO.File.ReadAllLines(path);
            //path = @"D:\zz_doktora\ourpapers\2017\IMP-Linear\dataset\ruthmaier_socnet\" + filename + ".txt";
            arc_set = new List<string>();

            var readData = (File.ReadLines(path).Skip(0).Select(a => {
                //string[] nodes_string_arr = a.Split(' ');
                //var temparc = nodes_string_arr[0] + "," + nodes_string_arr[1];
                //return new { Head = int.Parse(nodes_string_arr[0]), Tail = int.Parse(nodes_string_arr[1]),Id = a };
                return new { Id = a };
            }).AsParallel().ToList());

            if (arc_weights_ON==0)
            {
                unique_arcs = readData.GroupBy(a => a.Id).Select(a => new { Key = a, Count = a.Count() }).Select(a =>
            new ReadData
            {
                Key = new { Head = int.Parse(a.Key.Key.Split(',')[0]), Tail = int.Parse(a.Key.Key.Split(',')[1]) },
                Count = a.Count,
                W = (a.Count == 1) ? fixed_probability : (1 - Math.Pow((1 - fixed_probability), a.Count)),
            }).AsParallel().ToList();
            }

            else
            {
                unique_arcs = readData.GroupBy(a => a.Id).Select(a => new { Key = a, Count = a.Count() }).Select(a =>
                new ReadData
                {
                    Key = new { Head = int.Parse(a.Key.Key.Split(';')[0]), Tail = int.Parse(a.Key.Key.Split(';')[1]) },
                    Count = a.Count,
                    W = double.Parse(a.Key.Key.Split(';')[2]),
                }).AsParallel().ToList();
            }


            //new ReadData
            //{
            //    Key = new { Head = int.Parse(a.Key.Key.Split(',')[0]), Tail = int.Parse(a.Key.Key.Split(',')[1]) },
            //    Count = a.Count,
            //    W = Double.Parse(a.Key.Key.Split(',')[2]),
            //}).AsParallel().ToList();

            var nodes = unique_arcs.Select(a => a.Key.Head).Distinct().Union(unique_arcs.Select(b => b.Key.Tail).Distinct()).Distinct().AsParallel().ToList();
            //var left_nodes_neighbours = unique_arcs.GroupBy(a => a.Key.Head).Select(a => new { Head = a.Key, RefList = a.Select(b => b.Key.Tail).ToList() }).AsParallel().ToList();


            //List<ReadData> UniqueArcs = new List<ReadData>();
            //UniqueArcs.AddRange(unique_arcs);
            //UniqueArcs = unique_arcs.Select(a => a).AsParallel().ToList();



            result_set = new List<int>();
            N = nodes.Count;
            E = unique_arcs.Count;
            node_set = new List<int>();
            for (int i = 0; i < N; i++)
                node_set.Add((int)nodes[i]);

            //// ---- PARAMETERS



            //y_obj = new double[N];      // reduced modeldeki y katsayıları
            recruitment_cost = new double[N];
            //int budget_low = 1;
            //int budget_max = 100;

            if (is_BUDGETED == 1)
            {
                string[] lines_budget = System.IO.File.ReadAllLines(@"d:\Influence-marketing\Code\influencer-1\budget-10k.txt");
                for (int i = 0; i < N; i++)
                {
                    recruitment_cost[i] = System.Convert.ToDouble(lines_budget[i]);
                    //recruitment_cost[i] = r.Next(1, (int)BUDGET) / (BUDGET);
                    //recruitment_cost[i] = i / 10 + 1;
                }
                //recruitment_cost[0] = 1; recruitment_cost[1] = 3; recruitment_cost[2] = 2; recruitment_cost[3] = 5; recruitment_cost[4] = 1; recruitment_cost[5] = 2; recruitment_cost[6] = 4; recruitment_cost[7] = 6; recruitment_cost[8] = 3; recruitment_cost[9] = 5; recruitment_cost[10] = 3; recruitment_cost[11] = 2; recruitment_cost[12] = 4; recruitment_cost[13] = 5; recruitment_cost[14] = 7; recruitment_cost[15] = 6; recruitment_cost[16] = 5; recruitment_cost[17] = 6; recruitment_cost[18] = 4; recruitment_cost[19] = 5; recruitment_cost[20] = 6; recruitment_cost[21] = 5; recruitment_cost[22] = 4;
            }
            else
            {
                for (int i = 0; i < N; i++)
                {
                    //recruitment_cost[i] = System.Convert.ToDouble(lines_budget[i]);
                    recruitment_cost[i] = 1;
                    //recruitment_cost[i] = i / 10 + 1;
                }
                BUDGET = k_init;

            }

            System.Console.WriteLine("Finished Advanced Initialization");
            //test();

        }

        public static void test()
        {
            sw.Reset(); sw.Start();
            string temp = "";
            for (int i = 0; i < E; i++)
                temp = temp + arc_set[i];
            sw.Stop(); sw_elapsed = sw.Elapsed; double t1 = System.Convert.ToDouble(sw_elapsed.Ticks); System.Console.WriteLine("t1:" + t1);
            sw.Reset(); sw.Start();
            List<string> templ = new List<string>();
            for (int i = 0; i < E; i++)
                templ.Add(arc_set[i]);
            sw.Stop(); sw_elapsed = sw.Elapsed; t1 = System.Convert.ToDouble(sw_elapsed.Ticks); System.Console.WriteLine("t1:" + t1);
            System.Console.WriteLine("test finished");
        }

        public static void initialize_neighbourhood()  // create the actual neighbourhood list
        {
            //no_of_active_set = new int[trial_limit];

            neigh_list = new List<List<int>>();
            neigh_edge_list = new List<List<int>>();
            pred_list = new List<List<int>>();

            for (int i = 0; i < N; i++)
            {
                neigh_list.Add(new List<int>());
                neigh_edge_list.Add(new List<int>());
                pred_list.Add(new List<int>());
            }

            int neigh_loc;
            int neigh_loc2;
            int method = 1;

            // Write the neighbours and predecessors for the full network

            sw.Reset(); sw.Start();
            for (int j = 0; j < E; j++)
            {
                neigh_loc = arcs_intID[j, 0];     //arcs_int arrayındaki j. arkın 1.elemanının node_set listesindeki indeksi
                neigh_loc2 = arcs_intID[j, 1];   //arcs_int arrayındaki j. arkın 2.elemanının node_set listesindeki indeksi
                if (j % 1000 == 0)
                    System.Console.Write("-" + j);
                //successor set
                if (method == 1)
                {
                    neigh_list[neigh_loc].Add(node_set[neigh_loc2]);
                    neigh_edge_list[neigh_loc].Add(j);
                    pred_list[neigh_loc2].Add(node_set[neigh_loc]);
                }
            }
            sw.Stop(); sw_elapsed = sw.Elapsed; double t1 = System.Convert.ToDouble(sw_elapsed.Ticks); System.Console.WriteLine("t1:" + t1);
            System.Console.WriteLine("Finished initialize_neighbourhood");
        }

        public static void initialize_SAA_neighbourhood(int sample_size)
        {
            SAA_neigh_list = new List<List<List<int>>>();
            SAA_pred_list = new List<List<List<int>>>();
            List<double> SAA_latin_probs = new List<double>();
            List<List<int>> SAA_latin_PR = new List<List<int>>();
            x_exist = new bool[N, sample_size];
            double u = 0;
            for (int r = 0; r < sample_size; r++)
            {
                SAA_neigh_list.Add(new List<List<int>>());
                SAA_pred_list.Add(new List<List<int>>());
                if (run_LATIN == 1)
                {
                    SAA_latin_PR.Add(new List<int>());
                    for (int i = 0; i < N; i++)
                    {
                        SAA_latin_PR[r].Add(r + 1);
                    }
                }

                for (int i = 0; i < N; i++)
                {
                    x_exist[i, r] = false;
                    SAA_neigh_list[r].Add(new List<int>());
                    SAA_pred_list[r].Add(new List<int>());
                    if (run_LATIN == 1)
                    {
                        foreach (int edge in neigh_edge_list[i])   //arcID'leri tek tek işleyelim
                        {
                            u = (1.0 / sample_size) * (SAA_latin_PR[r][i] - 1 + GetUniform()); //+epsilon
                            SAA_latin_probs.Add(u);     //ExR random numbers, but unshuffled
                        }
                    }
                }
            }
            if (run_LATIN == 1)
                Shuffle(SAA_latin_probs);
            double prob;
            int counter = 0;
            int counter2 = 0;
            int curr_neighID = 0;
            int curr_neigh = -1;
            //StreamWriter swtemp = new StreamWriter("prob1.txt");
            for (int r = 0; r < sample_size; r++)
            {
                if (r % 10 == 0)
                    System.Console.Write("-" + r);
                for (int i = 0; i < N; i++)
                {
                    if (neigh_edge_list[i] != null)
                    {
                        foreach (int edge in neigh_edge_list[i])   //arcID'leri tek tek işleyelim
                        {
                            // ****** if node representation add node_set[]
                            curr_neighID = (int)arcs_intID[edge, 1];
                            curr_neigh = (int)node_set[curr_neighID];

                            if (run_LATIN == 1)
                                prob = SAA_latin_probs[counter];
                            else
                                prob = GetUniform();
                            counter++;
                            //swtemp.WriteLine(prob);


                            prop_prob = 1 - weight_set[(int)edge];
                            if (prob > prop_prob)
                            {
                                counter2++;
                                //successor set
                                SAA_neigh_list[r][i].Add(curr_neighID);  //curr_neigh ile yazılmıştı eskiden

                                //predecessor set
                                SAA_pred_list[r][curr_neighID].Add((int)i); //keeps nodeIDs not actual node names
                            }
                        }
                    }


                }   //end of for->nodes
            }       //end of for-> N1
            //swtemp.Close();
            System.Console.WriteLine("Counter:" + counter + " & Counter2:" + counter2);

        }  //create stochastic neighbourhood list for each node, for each sample, for each batch

        public static void initialize_SAA_neighbourhood_fast(int sample_size, List<dynamic> reslist)
        {
            System.Console.WriteLine("Starting Fast SAA_Neigh");
            SAA_neigh_list = new List<List<List<int>>>();
            SAA_pred_list = new List<List<List<int>>>();
            int counter2 = 0;
            x_exist = new bool[sample_size, N];
            //List<DirectedListGraph<int,UnweightedEdge>> m_list = new List<DirectedListGraph<int, UnweightedEdge>>();

            int Nmax = node_set.Max() + 1;
            node_index = new int[Nmax];
            for (int i = 0; i < N; i++)
            {
                node_index[node_set[i]] = i;
            }
            //x_exist = new bool[N, sample_size];

            for (int r = 0; r < sample_size; r++)
            {
                SAA_neigh_list.Add(new List<List<int>>());
                SAA_pred_list.Add(new List<List<int>>());
                //var m = new DirectedListGraph<int, UnweightedEdge>();
                for (int i = 0; i < N; i++)
                {
                    //x_exist[i, r] = true;
                    SAA_neigh_list[r].Add(new List<int>());
                    SAA_pred_list[r].Add(new List<int>());
                    //m.AddVertex(i);
                }
                //m_list.Add(m);
            }

            int head, tail;

            for (int r = 0; r < sample_size; r++)
            //Parallel.For(0, sample_size, r =>
            {
                foreach (BaseModel item in reslist[r])
                {
                    head = node_index[(int)item.Head];
                    tail = node_index[(int)item.Tail];
                    SAA_neigh_list[r][head].Add(tail);
                    SAA_pred_list[r][tail].Add(head);
                    counter2++;
                    //m_list[r].AddEdge(new UnweightedEdge(head, tail));
                }
            }
            //);
            //swtemp.Close();
            System.Console.WriteLine("Finished Fast Neigh! ...... Counter:" + E * SAA_N1 + " & Counter2:" + counter2);
            //determine_network_trees_IM(sample_size, m_list);
        }  //create stochastic neighbourhood list for each node, for each sample, for each batch


        public static void initialize_neighbourhood_fast_Tiptop()
        {
            System.Console.WriteLine("Starting Edge Neighbourhood for Tiptop");
            Tiptop_w_list = new List<List<Double>>();
            Tiptop_pred_list = new List<List<int>>();
            int counter = 0;

            int Nmax = node_set.Max() + 1;
            node_index = new int[Nmax];
            for (int i = 0; i < N; i++)
            {
                node_index[node_set[i]] = i;
                Tiptop_pred_list.Add(new List<int>());
                Tiptop_w_list.Add(new List<double>());
            }
            ////x_exist = new bool[N, sample_size];

            int head, tail;
            Double weight;

            foreach (var item in unique_arcs)
            {
                head = node_index[(int)item.Key.Head];
                tail = node_index[(int)item.Key.Tail];
                weight = item.W;
                Tiptop_w_list[tail].Add(weight);
                Tiptop_pred_list[tail].Add(head);
                counter++;
            }
            //}
            ////);
            ////swtemp.Close();
            System.Console.WriteLine("Finished Fast Neigh! ...... Counter:" + counter);
            ////determine_network_trees_IM(sample_size, m_list);
        }


        public static void initialize_random_arcs()
        {
            var reslist = new List<dynamic>();
            var tasks = new List<Task<List<BaseModel>>>();
            var rand = new Random();
            for (int i = 0; i < E; i++)
            {
                unique_arcs[i].Prop = rand.NextDouble();
            }

            for (int i = 0; i < SAA_N1; i++)
            {
                var luckyarcs = Task.Run<List<BaseModel>>(() => unique_arcs.Select(a => a).Where(a => (a.W >= a.GetProbablity())).AsParallel().ToList().Select(b =>
                            new BaseModel { Head = b.Key.Head, Tail = b.Key.Tail }).AsParallel().ToList());
                tasks.Add(luckyarcs);
                //var luckyarcs = unique_arcs.Select(a => a).Where(a => (a.W >= GetUniform())).AsParallel().ToList().Select(b =>
                //               new BaseModel { Head = b.Key.Head, Tail = b.Key.Tail }).AsParallel().ToList();
                //reslist.Add(luckyarcs);
            }
            var results = Task.WhenAll(tasks);
            foreach (var task in tasks)
            {
                var l1 = task.Result;
                reslist.Add(l1);
            }
            initialize_SAA_neighbourhood_fast(SAA_N1, reslist);
        }

        public static void initialize_random_arcs_LT(int sample_size)
        {
            System.Console.WriteLine("Starting Fast SAA_Neigh LT");
            SAA_neigh_list = new List<List<List<int>>>();
            SAA_pred_list = new List<List<List<int>>>();
            int counter2 = 0;
            x_exist = new bool[sample_size, N];

            int Nmax = node_set.Max() + 1;
            node_index = new int[Nmax];
            for (int i = 0; i < N; i++)
            {
                node_index[node_set[i]] = i;
            }
            //x_exist = new bool[N, sample_size];

            for (int r = 0; r < sample_size; r++)
            {
                SAA_neigh_list.Add(new List<List<int>>());
                SAA_pred_list.Add(new List<List<int>>());
                //var m = new DirectedListGraph<int, UnweightedEdge>();
                for (int i = 0; i < N; i++)
                {
                    //x_exist[i, r] = true;
                    SAA_neigh_list[r].Add(new List<int>());
                    SAA_pred_list[r].Add(new List<int>());
                    //m.AddVertex(i);
                }
                //m_list.Add(m);
            }

            neigh_list = new List<List<int>>();
            for (int i = 0; i < N; i++)
            {
                neigh_list.Add(new List<int>());
            }

            int current_head = 0; ;
            int current_tail = 0; ;

            for (int i = 0; i < E; i++)
            {
                current_head = node_index[(int)unique_arcs[i].Key.Head];
                current_tail = node_index[(int)unique_arcs[i].Key.Tail];
                neigh_list[current_head].Add(current_tail);
            }

            var rand = new Random();
            double rand_number = 0;
            int neigh_order = 0;

            for (int r = 0; r < sample_size; r++)
            {
                for (int i = 0; i < N; i++)
                {
                    neigh_order = neigh_list[i].Count;
                    if (neigh_order > 0)
                    {
                        rand_number = Math.Floor(rand.NextDouble() * neigh_order);
                        SAA_neigh_list[r][i].Add(neigh_list[i][(int)rand_number]);
                        SAA_pred_list[r][(int)neigh_list[i][(int)rand_number]].Add((int)i);
                    }
                }
            }
        }

        public static List<double> Shuffle(List<double> array)
        {
            int n = array.Count;
            Random rng = new Random();
            double tmp = 0;
            while (n > 1)
            {
                int k = rng.Next(n--);
                tmp = array[n];
                array[n] = array[k];
                array[k] = tmp;
            }
            return array;
        }

        public static void initialize_SAA_1_prb(int SAA_m)  // create probabilities for objective function calculation diffusion with a large sample size
        {
            double prob;
            SAA_1_prb = new double[E, SAA_N1];

            for (int c = 0; c < E; c++)
            {
                for (int b = 0; b < SAA_N1; b++)
                {
                    //for (int a = 0; a < SAA_M; a++)
                    {
                        prob = GetUniform();
                        SAA_1_prb[c, b] = prob;
                    }
                }
            }
        }

        public static void initialize_SAA_2_prb(int SAA_m)  // create probabilities for objective function calculation diffusion with a large sample size
        {
            double prob;
            SAA_2_prb = new double[E, SAA_N2];

            for (int c = 0; c < E; c++)
            {
                for (int b = 0; b < SAA_N2; b++)
                {
                    //for (int a = 0; a < SAA_M; a++)
                    {
                        prob = GetUniform();
                        SAA_2_prb[c, b] = prob;
                    }
                }
            }
        }

        public static void initialize_SAA_Float()  // create probabilities for objective function calculation diffusion with a large sample size
        {
            float prob;
            SAA_float = new float[E, SAA_N2];

            for (int c = 0; c < E; c++)
            {
                for (int b = 0; b < SAA_N2; b++)
                {
                    //for (int a = 0; a < SAA_M; a++)
                    {
                        prob = (float)GetUniform();
                        SAA_float[c, b] = prob;
                    }
                }
            }
        }

        public static void initialize_SAA_3_prb()  // create probabilities for the final objective function calculation diffusion with a large sample size
        {
            double prob;
            //SAA_prob = new double[E, SAA_N1, SAA_M];

            SAA_3_prob = new double[E, SAA_N3];
            for (int c = 0; c < E; c++)
            {
                for (int b = 0; b < SAA_N3; b++)
                {
                    prob = GetUniform();
                    SAA_3_prob[c, b] = prob;

                }
            }
        }

        public static void initialize_SAA_3_prb_list()  // create probabilities for the final objective function calculation diffusion with a large sample size
        {
            double prob;
            //SAA_prob = new double[E, SAA_N1, SAA_M];

            SAA_3_prob_dbl = new List<List<double>>();
            for (int c = 0; c < E; c++)
            {
                List<double> templist = new List<double>();
                for (int b = 0; b < SAA_N3; b++)
                {
                    prob = GetUniform();
                    templist.Add(prob);

                }
                SAA_3_prob_dbl.Add(templist);
            }
        }

       public static void TIPTOP()
        {
            //if (run_reduction == 1)
            //  reduce_tree_list();
            System.Console.WriteLine("Solving with TIPTOP!");
            double result = mip_TIPTOP();
        }

        public static void SAA_linderoth()
        {

            //trial_limit = SAA_N1;
            SA_1_obj = new double[SAA_M];
            y_obj = new double[N];

            double max_obj = -1;
            //int type = 1; //SAA'ya gir-1
            SA_1_test_obj = new double[SAA_M];
            SAA_list = new List<List<int>>(SAA_M);
            SAA_pipage_list = new List<List<int>>(SAA_M);
            SAA_LR_list = new List<List<int>>(SAA_M);
            string SAA_str_solution = "";
            Double dt_IP = 0; Double dt_PipageP = 0; Double dt_greedy = 0; Double dt_LR = 0;
            int k;

            double[] LP_arr = new double[SAA_M]; double[] LR_UB_arr = new double[SAA_M];
            double[] IP_arr = new double[SAA_M]; double[] LR_LB_arr = new double[SAA_M];
            double[] LP_inf = new double[SAA_M]; double[] LR_inf_arr = new double[SAA_M];
            string[] sol_arr = new string[SAA_M]; string[] LR_sol_arr = new string[SAA_M];
            double tot_LP = 0; double tot_IP = 0; double avg_LP = 0; double avg_IP = 0; double best_IP = 0; int best_index_LP = -1;
            double LR_tot_UB = 0; double LR_tot_LB = 0; double LR_avg_UB = 0; double LR_avg_LB = 0; double LR_best_inf = 0; int LR_best_index = -1; string LR_best_seed = "";
            double LR_UB_std = 0;
            double LR_inf_std = 0;
            double LR_total_inf = 0;

            List<int> temp_list = new List<int>();


            if (is_BUDGETED != 1)
            {
                BUDGET = k_init;
            }



            if (run_MIP == 1 || run_pipage == 1 || run_LR == 1)
            {
                Stopwatch sw_pipage = new Stopwatch(); pipage_count = ""; Stopwatch sw_LR = new Stopwatch();
                Stopwatch swx = new Stopwatch();
                double temp_obj = 0;
                int max_index = -1;
                swx.Start();
                for (int i = 0; i < SAA_M; i++)
                {

                    if (runLT == 1)
                        initialize_random_arcs_LT(SAA_N1);
                    else
                        initialize_random_arcs();

                    theoption = 0;
                    //initialize_SAA_neighbourhood(SAA_N1);
                    if (run_MIP == 1 || run_pipage == 1 || run_reduction == 1 || run_LR == 1)
                    {
                        //if (run_MEM == 1)
                        //determine_network_trees_mem(SAA_N1);
                        //else
                        determine_network_trees(SAA_N1);
                    }
                    swx.Stop(); System.Console.WriteLine(swx.Elapsed.Ticks); swx.Reset();
                    // if (run_LR == 1)
                    //  determine_fwd_network_trees_list(SAA_N1);
                    if (run_reduction == 1)
                        reduce_tree_list();

                    if (run_MIP == 1)
                    {
                        sw.Start();
                        System.Console.WriteLine("Solving " + (i + 1) + "-th SAA problem");
                        SA_1_obj[i] = mip_model(i, 0, SAA_N1);
                        temp_obj = temp_obj + SA_1_obj[i];
                        sw.Stop();
                        System.Console.WriteLine(sw.ElapsedTicks);
                        dt_IP = sw.ElapsedMilliseconds;
                    }

                    if (run_pipage == 1)
                    {
                        sw_pipage.Start();
                        System.Console.WriteLine("Solving " + (i + 1) + "-th LP-SAA problem");
                        pipage_objective_LP = (double)construct_model2_gurobi_LP(i, 1, SAA_N1, 0) / SAA_N1;
                        System.Console.WriteLine("Pipage Integer objective: " + pipage_objective_LP + "-" + pipage_objective_IP);
                        System.Console.WriteLine("Pipage seed: " + pipage_solution);
                        tot_LP = tot_LP + pipage_objective_LP; tot_IP = tot_IP + pipage_objective_IP;
                        LP_arr[i] = pipage_objective_LP; IP_arr[i] = pipage_objective_IP; sol_arr[i] = pipage_solution;
                        LP_inf[i] = evaluate_influence(SAA_pipage_list[i], i, SAA_N2, 2);

                        //i++;
                        //pipage_objective_LP = (double)construct_model2_gurobi_LP(i, 2, SAA_N1, 0) / SAA_N1;
                        //LP_arr[i] = pipage_objective_LP; IP_arr[i] = pipage_objective_IP; sol_arr[i] = pipage_solution;
                        //LP_inf[i] = evaluate_influence(SAA_pipage_list[i], i, SAA_N2, 2);
                        System.Console.WriteLine("Point estimate :" + LP_inf[i]);

                        if (LP_inf[i] > best_IP)
                        {
                            best_IP = LP_inf[i]; best_index_LP = i; System.Console.WriteLine("New best found at batch " + (i + 1));
                        }
                        sw_pipage.Stop();
                        TimeSpan sw_pipage_elapsed = sw_pipage.Elapsed; pipage_T = System.Convert.ToDouble(sw_pipage_elapsed.Ticks);
                    }

                    if (run_LR == 1)
                    {
                        sw_LR.Start();
                        //z_LRUB is written in function, z_LRLB is what function returns (feasible solution), zLRinf, t_LR
                        //initialize_SAA_neighbourhood(SAA_N1); //determine_network_trees(SAA_N1);
                        //theoption = 1;  determine_network_trees(SAA_N1);
                        //determine_fwd_network_trees_list(SAA_N1);
                        //double initialize_duals= (double)construct_model2_gurobi_LP(i, 0, 1, 0);
                        //LR_LB_arr[i] = (double)LR_3_Shabbir(i, 0, SAA_N1) / SAA_N1;
                        //determine_network_trees_mem(SAA_N1);
                        //if (run_MEM == 1)
                        //  LR_LB_arr[i] = (double)LR_0_mem(i, 0, SAA_N1) / SAA_N1;
                        //else
                        LR_LB_arr[i] = (double)LR_0(i, 0, SAA_N1) / SAA_N1;
                        //double LR2_result= (double)LR_0(i, 1, SAA_N1) / SAA_N1;
                        //if (LR_LB_arr[i]> LR2_result)
                        //{
                        //    System.Console.WriteLine("LR1 : " + LR_LB_arr[i] + " LR2 : +" + LR2_result);
                        //}



                        //myoption = 0; LR_LB_arr[i] = (double)LR_0(i, 1, SAA_N1) / SAA_N1;

                        //reduce_tree_list();
                        //theoption = 1;
                        //swx.Start();
                        //determine_network_trees(SAA_N1); swx.Stop(); System.Console.WriteLine(swx.Elapsed.Ticks); swx.Reset();
                        //LR_LB_arr[i] = (double)LR_0(i, 1, SAA_N1) / SAA_N1;

                        //swx.Start(); determine_network_trees_mem(SAA_N1); swx.Stop(); System.Console.WriteLine(swx.Elapsed.Ticks); swx.Reset();
                        //LR_LB_arr[i] = (double)LR_0_mem(i, 1, SAA_N1) / SAA_N1;
                        //LR_LB_arr[i] = (double)LR_0(i, 1, SAA_N1) / SAA_N1;
                        LR_UB_arr[i] = z_LRUB;
                        LR_sol_arr[i] = solution_LR;
                        sw_LR.Stop();
                        double sw_LR_elapsed = sw_LR.ElapsedMilliseconds; t_LR = sw_LR_elapsed;
                    }

                }


                //reporting

                if (run_MIP == 1)
                {
                    sw.Reset(); sw.Start();
                    SA_1_hat_obj = temp_obj / SAA_M;

                    R1_avg = SA_1_hat_obj;
                    R1_var = 0;
                    for (int i = 0; i < SAA_M; i++)
                    {
                        R1_var = R1_var + (R1_avg - SA_1_obj[i]) * (R1_avg - SA_1_obj[i]);
                    }
                    R1_var = R1_var / (SAA_M - 1);
                    R1_std = Math.Sqrt(R1_var);

                    string[] stringsArray;
                    string the_vars_list;

                    temp_obj = 0;
                    System.Console.WriteLine("SAA upperbund : " + SA_1_hat_obj);
                    SA_2_obj = new double[SAA_M];
                    //SAA-2'leri LP olarak çözeceksen bu iki satırı açman gerek
                    //initialize_SAA_neighbourhood(SAA_M, SAA_N2);
                    //determine_network_depth(SAA_N2);
                    T_LB = new double[SAA_M];
                    for (int i = 0; i < SAA_M; i++)
                    {
                        stringsArray = SAA_list[i].Select(the_i => the_i.ToString()).ToArray();
                        the_vars_list = string.Join(",", stringsArray);

                        T_LB[i] = 0;

                        for (int j = 0; j < SAA_T; j++)
                        {
                            //initialize_SAA_2_prb(i * SAA_M + j);
                            SAA_current_list = new List<int>(SAA_list[i]);
                            temp_obj = evaluate_influence(SAA_list[i], i, SAA_N2, 1);
                            T_LB[i] = T_LB[i] + temp_obj;
                            System.Console.WriteLine("Evaluating x: " + the_vars_list + ", and " + (i + 1) + "-th objective (" + SA_1_obj[i] + ") -->" + T_LB[i]);
                        }
                        T_LB[i] = T_LB[i] / SAA_T;


                        if (T_LB[i] > max_obj)
                        {
                            max_obj = T_LB[i];
                            max_index = i;
                        }
                        SA_2_obj[i] = T_LB[i];
                        //temp_obj = mip_model(i, 1, SAA_N2); ;
                        //SAA_list_string = string.Join(",", );

                    }

                    max_obj = SA_2_obj[max_index];
                    System.Console.WriteLine("Re-Evaluating " + (max_index + 1) + "-th objective with influence : " + max_obj);


                    // STEP - 3 OF SAA METHOD
                    T2_avg = 0;
                    T2_LB = new double[SAA_T];
                    for (int j = 0; j < SAA_T; j++)
                    {
                        //initialize_SAA_3_prb();
                        T2_LB[j] = evaluate_influence(SAA_list[max_index], 0, SAA_N3, 2);
                        T2_avg = T2_avg + T2_LB[j];
                    }
                    T2_avg = T2_avg / SAA_T;
                    T2_var = 0;
                    for (int j = 0; j < SAA_T; j++)
                    {
                        T2_var = T2_var + (T2_avg - T2_LB[j]) * (T2_avg - T2_LB[j]);
                    }
                    T2_var = T2_var / (SAA_T - 1);
                    T2_std = Math.Sqrt(T2_var);

                    SA_3_obj = T2_avg;


                    //int[] st_arr = SAA_list[max_index].ToArray();

                    k = SAA_list[max_index].Count;
                    SAA_list[max_index].Sort();
                    //string SAA_str_solution = "";
                    for (int i = 0; i < k; i++)
                    {
                        //sww.WriteLine(result_set[i]);
                        SAA_str_solution = SAA_str_solution + "," + node_set[(int)SAA_list[max_index][i]];
                    }

                    sw.Stop(); dt_IP = dt_IP + sw.ElapsedMilliseconds;

                    System.Console.WriteLine("-------------summary---------------");
                    System.Console.WriteLine("SA_1_hat : " + SA_1_hat_obj);
                    System.Console.WriteLine("SA_2* : " + max_obj + " the " + (max_index + 1) + "-th sample");
                    System.Console.WriteLine("SA_3* : " + SA_3_obj);
                    System.Console.WriteLine("Optimality Gap : " + (SA_1_hat_obj - SA_3_obj) + " (% " + 100 * (SA_1_hat_obj - SA_3_obj) / SA_3_obj + ")");
                    System.Console.WriteLine("Time : " + System.Convert.ToDouble(dt_IP / 10000000.0));
                    swvar.WriteLine("SA_1_hat : " + SA_1_hat_obj);
                    swvar.WriteLine("SA_2* : " + max_obj + " the " + (max_index + 1) + "-th sample");
                    swvar.WriteLine("SA_3* : " + SA_3_obj);
                    swvar.WriteLine("Optimality Gap : " + (SA_1_hat_obj - SA_3_obj) + " (% " + 100 * (SA_1_hat_obj - SA_3_obj) / SA_3_obj + ")");
                }


                if (run_pipage == 1)
                {
                    avg_IP = tot_IP / SAA_M; avg_LP = tot_LP / SAA_M;
                    //sw.Stop(); sw_elapsed = sw.Elapsed; pipage_T = System.Convert.ToDouble(sw_elapsed.Ticks);
                    System.Console.WriteLine("\r\n ---- LP Solutions---");
                    System.Console.WriteLine("Sample Averages (IP/LP): " + avg_IP + "/" + avg_LP);
                    System.Console.WriteLine("Best seed: " + sol_arr[best_index_LP]);
                    System.Console.WriteLine("Best Objective Value Estimate: " + best_IP);
                    System.Console.WriteLine("Corresponding LP/IP Obj. Values : " + LP_arr[best_index_LP] + "/" + IP_arr[best_index_LP]);
                    System.Console.WriteLine("Time : " + System.Convert.ToDouble(pipage_T / 10000000.0));
                    System.Console.WriteLine("pipage_count : " + pipage_count);

                    z_pipageInf = best_IP;
                    pipage_objective_LP = avg_LP;
                    pipage_objective_IP = avg_IP;
                    pipage_solution = sol_arr[best_index_LP];

                    if (best_index_LP != 0)
                    {
                        System.Console.WriteLine("Best Index:" + (best_index_LP + 1));
                    }

                }


                //LR results

                if (run_LR == 1)
                {
                    int inf_method = 0;
                    if (SAA_M > 100)
                    {
                        initialize_SAA_Float();
                        inf_method = 6;
                    }
                    else
                    {
                        inf_method = 2;
                    }
                    for (int i = 0; i < SAA_M; i++)
                    {

                        LR_inf_arr[i] = evaluate_influence(SAA_LR_list[i], i, SAA_N2, inf_method);
                        //LR_inf_arr[i] = i+1;
                        System.Console.WriteLine(i + "-->" + LR_UB_arr[i] + "/" + LR_LB_arr[i] + "  inf: " + LR_inf_arr[i]);
                        if (LR_inf_arr[i] > LR_best_inf)
                        {
                            LR_best_seed = LR_sol_arr[i]; LR_best_inf = LR_inf_arr[i]; LR_best_index = i; System.Console.WriteLine("New best found at batch " + (i + 1));
                        }
                        LR_tot_UB = LR_tot_UB + LR_UB_arr[i]; LR_tot_LB = LR_tot_LB + LR_LB_arr[i]; LR_total_inf = LR_total_inf + LR_inf_arr[i];
                    }
                    LR_avg_UB = LR_tot_UB / SAA_M; LR_avg_LB = LR_tot_LB / SAA_M;

                    for (int i = 0; i < SAA_M; i++)
                    {
                        LR_UB_std = LR_UB_std + (LR_UB_arr[i] - LR_avg_UB) * (LR_UB_arr[i] - LR_tot_UB / SAA_M);
                        LR_inf_std = LR_inf_std + (LR_inf_arr[i] - LR_total_inf / SAA_M) * (LR_inf_arr[i] - LR_total_inf / SAA_M);
                    }
                    LR_UB_std = Math.Sqrt(LR_UB_std / SAA_M); LR_inf_std = Math.Sqrt(LR_inf_std / SAA_M);


                    //sw.Stop(); sw_elapsed = sw.Elapsed; pipage_T = System.Convert.ToDouble(sw_elapsed.Ticks);
                    System.Console.WriteLine("\r\n ---- LR-1 Solutions---");
                    System.Console.WriteLine("Sample Averages (IP/LP): " + LR_avg_UB + "/" + LR_avg_LB);
                    System.Console.WriteLine("Best seed: " + LR_sol_arr[LR_best_index]);
                    System.Console.WriteLine("Best Objective Value Estimate: " + LR_inf_arr[LR_best_index]);
                    System.Console.WriteLine("Stdevs: " + LR_UB_std + " - " + LR_inf_std);
                    System.Console.WriteLine("Time : " + System.Convert.ToDouble(t_LR / 10000000.0));
                }

                sw.Reset(); sw_pipage.Reset(); sw_LR.Reset();
            }


            //CELF
            if (run_CELF == 1)
            {

                sw.Start();
                CELF_main();
                //for (int i = 0; i < SAA_M; i++)
                {
                    //System.Console.WriteLine("Solving " + (i + 1) + "-th CELF-Greedy");

                    //independent_cascade_lazy_forward_budgeted();
                }
                sw.Stop(); sw_elapsed = sw.Elapsed; CELF_t = System.Convert.ToDouble(sw_elapsed.Ticks);

                //manuel calculation
                //List<int> thelist = new List<int>(); thelist.Add(1); thelist.Add(6); thelist.Add(11);
                //double xxx = evaluate_influence(thelist, 0, SAA_N3, 2);

                //System.Console.ReadKey();
                //List<int> IMBP_sol = new List<int>(50);

            }
            string sqltext;
            string constr = "Server=localhost\\SQLExpress;Database=research;User Id=doktora;Password=cesmede;";
            SqlConnection conn = new SqlConnection(constr);
            conn.Open();
            SqlCommand command = conn.CreateCommand();

            if (run_CELF == 1)
            {
                for (int c_i = 0; c_i < k_init; c_i++)
                {
                    sqltext = "INSERT INTO BIMP_SAA (SAA_M,SAA_N1,SAA_N2,SAA_N3,modelID, diffusion_modelID,K,network_sampleID,node_size,edge_size,duration,z_star,SAA_z, SAA_z2, SAA_z3,solution_y, propagation_prop, budget,R1_std, T2_std,z_pipageLP,z_pipageIP,z_pipageInf,t_pipage,z_greedy,t_CELF,pipage_solution,CELF_solution, z_LRUB, z_LRLB, zLRinf,t_LR, solution_LR ) VALUES (" + SAA_M + "," + SAA_N1 + "," + SAA_N2 + "," + SAA_N3 + ",1,1," + (k_init - c_i) + ",1," + N + "," + E + "," + dt_IP + ",-1," + SA_1_hat_obj + "," + max_obj + "," + SA_3_obj + ",'" + SAA_str_solution + "'," + prop_prob + ",'" + BUDGET + "','" + R1_std + "','" + T2_std + "'," + pipage_objective_LP + "," + pipage_objective_IP + "," + z_pipageInf + "," + pipage_T + "," + CELF_z_arr[c_i] + "," + CELF_t_arr[c_i] + ",'" + pipage_solution + "','" + CELF_sol_arr[c_i] + "'," + LR_avg_UB + "," + LR_avg_LB + "," + LR_best_inf + "," + t_LR + ",'" + LR_best_seed + "')";
                    sqltext = sqltext.Replace("'NaN'", "'0'");
                    command.CommandText = sqltext;
                    command.ExecuteNonQuery();
                }
            }
            else
            {
                sqltext = "INSERT INTO BIMP_SAA (SAA_M,SAA_N1,SAA_N2,SAA_N3,modelID, diffusion_modelID,K,network_sampleID,node_size,edge_size,duration,z_star,SAA_z, SAA_z2, SAA_z3,solution_y, propagation_prop, budget,R1_std, T2_std,z_pipageLP,z_pipageIP,z_pipageInf,t_pipage,pipage_solution,pipage_count, z_LRUB, z_LRLB, z_LRinf,t_LR, solution_LR, stdev_LRUB, stdev_LRinf, fixed_p, LR_iter) VALUES (" + SAA_M + "," + SAA_N1 + "," + SAA_N2 + "," + SAA_N3 + ",1,1," + k_init + ",1," + N + "," + E + "," + dt_IP + ",-1," + SA_1_hat_obj + "," + max_obj + "," + SA_3_obj + ",'" + SAA_str_solution + "'," + prop_prob + ",'" + BUDGET + "','" + R1_std + "','" + T2_std + "'," + pipage_objective_LP + "," + pipage_objective_IP + "," + z_pipageInf + "," + pipage_T + ",'" + pipage_solution + "','" + pipage_count + "'," + LR_avg_UB + "," + LR_avg_LB + "," + LR_best_inf + "," + t_LR + ",'" + LR_best_seed + "'," + LR_UB_std + "," + LR_inf_std + "," + fixed_probability + "," + no_of_LR_iter + ")";
                sqltext = sqltext.Replace("'NaN'", "'0'");
                command.CommandText = sqltext;
                command.ExecuteNonQuery();
            }



            if (1 == 0)
            {
                command.CommandText = "select top 1 ID FROM BIMP_SAA order by ID desc";
                SqlDataReader reader = command.ExecuteReader();
                reader.Read();
                int theID = Convert.ToUInt16(reader["ID"]);
                reader.Close();
                string query = "";
                if (run_MIP == 1)
                {
                    for (int i = 0; i < SAA_M; i++)
                    {
                        k = SAA_list[i].Count;
                        SAA_list[i].Sort();
                        SAA_str_solution = "";
                        for (int j = 0; j < k; j++)
                        {
                            //sww.WriteLine(result_set[i]);
                            SAA_str_solution = SAA_str_solution + "," + node_set[(int)SAA_list[i][j]];
                        }
                        query = "INSERT INTO SAA_detail_solutions ( runID, solution_no,solution,z1,z2_avg) VALUES (" + theID + "," + (i + 1) + ",'" + SAA_str_solution + "'," + SA_1_obj[i] + "," + T_LB[i] + ")";
                        command.CommandText = query;
                        command.ExecuteNonQuery();

                    }
                }

            }
            command.Dispose();
            conn.Close();
            SAA_tree_list.Clear();
            //SAA_fwd_tree_list.Clear();
        }

        public static void finish()
        {
            //StreamWriter sww = new StreamWriter("result.txt");
            //for (int i = 0; i < result_set.Count; i++)
            {
                //sww.WriteLine(result_set[i]);
            }
            //sww.Close();
        }



        #region Greedy

        public static void CELF_main()
        {
            sw.Start();
            CELF_z_arr = new double[k_max];
            CELF_t_arr = new double[k_max];
            CELF_sol_arr = new string[k_max];
            BUDGET = k_init;

            //initialize_SAA_neighbourhood(SAA_M, SAA_N1);
            //initialize_SAA_3_prb(); directly use uniform
            independent_cascade_lazy_forward_budgeted();
            sw.Reset();
        }

        public static void independent_cascade_lazy_forward_budgeted()
        {
            result_set.Clear();
            init_set = new List<int>();
            selected_set = new List<int>();
            int current_k = 0;
            int iteration = 0;
            int M = SAA_M;
            double cumulative_time = 0;
            avg_no_AS = new double[N];
            StreamWriter celfSW = new StreamWriter("CELF.txt");
            for (int m = M - 1; m < M; m++)
            {
                //initialize_IC_probabilities(m, trial_limit);
                //initialization
                //initialize_IC_probabilities(0);
                int nodeID = 0;
                List<List<double>> priority_list = new List<List<double>>();
                SortedList<double, List<double>> mylist = new SortedList<double, List<double>>();
                double avg_no_AS_percost;
                //do it once
                for (int i = 0; i < N; i++)
                {
                    nodeID = node_set[i];
                    init_set.Add((int)i);
                    //nodeID = my_node_set[i];
                    //evaluate_influence(SAA_list[max_index], 0, SAA_N3, 2);

                    //avg_no_AS[i] = evaluate_influence(init_set, m, SAA_N1, 3); //Greedy'e özel evaluate influence için bu
                    avg_no_AS[i] = evaluate_influence(init_set, m, SAA_N2, 2);
                    avg_no_AS_percost = avg_no_AS[i] / recruitment_cost[i];

                    avg_no_AS_percost = avg_no_AS_percost + (i + 1) * 0.00000000001;
                    System.Console.WriteLine("seed : " + (i) + " ...Avg. Active:" + avg_no_AS[i] + " per cost :" + avg_no_AS_percost);
                    celfSW.WriteLine("seed : " + (i) + "N_" + node_set[i] + " ...Avg. Active:" + avg_no_AS[i] + " per cost :" + avg_no_AS_percost);
                    //System.Console.ReadKey();

                    List<double> sub_list = new List<double>();
                    sub_list.Add(avg_no_AS_percost);
                    sub_list.Add(0);
                    sub_list.Add(i);
                    sub_list.Add(avg_no_AS[i]);
                    mylist.Add(avg_no_AS_percost, sub_list);
                    init_set.Remove((int)i);
                }
                double total_cost = 0;
                celfSW.Close();
                // Lazy Forward Part
                int counter = 0;
                double previous_key = 0;
                double max_influence = 0;

                do
                {
                    current_k = iteration;
                    counter++;
                    double lastkey = mylist.Keys.Last();
                    int lastID = (int)mylist[lastkey][2];
                    int lastiteration = (int)mylist[lastkey][1];
                    if (iteration == 0)
                        max_influence = lastkey * recruitment_cost[lastID];
                    if (lastiteration == iteration)
                    {
                        if (total_cost + recruitment_cost[lastID] <= BUDGET)
                        {
                            selected_set.Add((int)lastID);
                            result_set.Add((int)lastID);
                            total_cost = total_cost + recruitment_cost[lastID];
                            System.Console.WriteLine("Selected " + (lastID) + " ...with:" + lastkey);
                            System.Console.WriteLine("Remaining Budget : " + (BUDGET - total_cost) + " out of " + BUDGET);
                            System.Console.WriteLine();
                            celfSW.WriteLine(string.Join(",", result_set.Select(the_i => the_i.ToString()).ToArray()) + "||" + lastkey + "||" + System.DateTime.Now.ToString());
                            //swvar.WriteLine("Selected " + (lastID) + " ...with:" + lastkey + " with total influence : " + max_influence);
                            CELF_z = max_influence;
                            //write_to_database();
                            sw.Stop(); sw_elapsed = sw.Elapsed; Double dt = System.Convert.ToDouble(sw_elapsed.Ticks); cumulative_time = dt; sw.Start();
                            CELF_z_arr[iteration] = max_influence;
                            CELF_t_arr[iteration] = cumulative_time;
                            CELF_sol_arr[iteration] = string.Join(" | ", result_set.Select(the_i => node_set[(int)the_i].ToString()).ToArray());

                            previous_key = max_influence;
                            iteration++;
                        }
                        mylist.Remove(lastkey);
                        //iteration++;
                    }
                    else
                    {
                        if (total_cost + recruitment_cost[lastID] <= BUDGET)
                        {
                            selected_set.Add((int)lastID);
                            // type-2, large sample, type-3 sample size equal to IP's sample size
                            double influence = evaluate_influence(selected_set, m, SAA_N2, 2); ;// evaluate_influence(selected_set, lastID, counter);
                            //double influence = evaluate_influence(selected_set, m, SAA_N1, 3); ;// evaluate_influence(selected_set, lastID, counter);
                            selected_set.Remove((int)lastID);
                            double marginal_gain = influence - previous_key;

                            avg_no_AS_percost = marginal_gain / recruitment_cost[lastID];

                            //influence = avg_no_AS_percost; // 2 of 3 for IMP, comment out this line
                            if (influence > max_influence)
                                max_influence = influence;
                            System.Console.WriteLine("Trying " + (lastID) + " with:" + lastkey.ToString("0.000000") + ", Inf : " + influence.ToString("0.0000") + " MG:" + marginal_gain.ToString("0.000000") + " NK: " + avg_no_AS_percost.ToString("0.000000"));
                            mylist.Remove(lastkey);
                            List<double> sub_list = new List<double>();
                            sub_list.Add(avg_no_AS_percost);
                            sub_list.Add(iteration);
                            sub_list.Add(lastID);
                            if (mylist.IndexOfKey(avg_no_AS_percost) == -1)
                                //marginal_gain = marginal_gain * 0.999999999999999999;
                                mylist.Add(avg_no_AS_percost, sub_list);
                        }
                        else
                        {
                            mylist.Remove(lastkey);
                            //iteration++;
                        }

                    }


                } //while (iteration < k_init); //3 of 3 change for IMP, activate this line, comment out the next
                while (total_cost <= BUDGET && mylist.Count > 0);

                //CELF_z_list[m] = max_influence;
                List<int> temp_list = new List<int>();
                for (int i = 0; i < selected_set.Count; i++)
                    temp_list.Add(selected_set[i]);
                CELF_solution = "";
                for (int i = 0; i < selected_set.Count; i++)
                {
                    CELF_solution = CELF_solution + "," + node_set[(int)selected_set[i]];
                }
                //CELF_solution_list.Add(temp_list);
                //CELF_solution_list_str[m] = list_to_string(selected_set);


                CELF_z = max_influence;
                double temp_obj = evaluate_influence(selected_set, 0, SAA_N3, 2);
                selected_set.Clear();
                result_set.Clear();

            }
            celfSW.Close();


        }
        #endregion

        #region formulation_v1_with_x_irt

        public static void determine_network_depth(int sample_size)
        {
            System.Console.WriteLine("Calculate T_ir for " + SAA_M * sample_size * N + " node-run-sample couples (takes 1-2 minutes)");
            int temp = 0;
            int max = 0;
            int nodeID = 0;
            network_depth = new int[N, sample_size, SAA_M];
            SAA_total_network_depth = new int[SAA_M];
            SAA_max_network_depth = new int[SAA_M];
            //for (int m = 0; m < SAA_M; m++)
            {
                for (int r = 0; r < sample_size; r++)
                {
                    for (int i = 0; i < N; i++)
                    {
                        if (SAA_pred_list[r][i].Count() > 0)
                        {
                            //                            nodeID = node_set[i];
                            temp = depth_with_BFS(i, r);
                            //depth_with_BFS(i, r, m);
                        }
                        else
                        {
                            temp = 0;
                        }

                        total_network_depth = total_network_depth + temp;
                        network_depth[i, r, 0] = temp;
                        if (temp > max)
                            max = temp;
                    }
                }
                SAA_total_network_depth[0] = total_network_depth;
                SAA_max_network_depth[0] = max;
                total_network_depth = 0;
                temp = 0;
                max = 0;

            }

            System.Console.WriteLine("Sum of network depth for " + sample_size * N + " is :" + total_network_depth);
        }

        public static int depth_with_BFS(int starting_node, int r) // determine the network depth by Breadth-first-search for each node - sample couple
        {
            List<int> temp_nodes = new List<int>();
            int[] node_colors = new int[N];
            int[] node_labels = new int[N];
            int starting_node_ID = node_set[starting_node];
            for (int i = 0; i < N; i++)
            {
                node_colors[i] = 0;
                node_labels[i] = -1;
            }
            int node_index = -1;
            string[] neigh_arr;
            int curr_neigh = 0;
            int curr_index = 0;

            temp_nodes.Add(starting_node);
            node_index = starting_node;
            int statint_node_index = starting_node;
            node_colors[node_index] = 1;
            node_labels[node_index] = 0;
            string arc = null;
            int arc_index = -1;
            double temp_arc_weight = 0;
            while (temp_nodes.Count != 0)
            {
                node_index = temp_nodes[0];
                //if (SAA_pred[node_index, r, m] != null)   // this is old string version
                if (SAA_pred_list[r][node_index].Count() > 0)
                {
                    //if (node_index == node_set.IndexOf(starting_node_ID))
                    //node_labels[node_index] = 1;
                    //neigh_arr = SAA_pred[node_index, r, m].Split(new char[] { ',' });     //neighbour stringini split edelim
                    //foreach (string str in neigh_arr)   //tüm komşuları aktifleştirmeye çalış
                    foreach (int node in SAA_pred_list[r][node_index])   //tüm komşuları aktifleştirmeye çalış
                    {
                        curr_index = (int)node;  //curr_index = Convert.ToUInt16(str);
                        if (node_colors[curr_index] == 0)
                        {
                            temp_nodes.Add(curr_index);
                            node_colors[curr_index] = 1;
                            if (curr_index != statint_node_index && node_labels[curr_index] == -1)
                                node_labels[curr_index] = node_labels[node_index] + 1;
                        }

                    }
                }
                temp_nodes.Remove(temp_nodes[0]);
                node_colors[node_index] = 2;
            }
            int result = node_labels.Max();
            //System.Console.WriteLine(result);
            return result;
        }

        #endregion

        // old version
        public static void determine_fwd_network_trees(int sample_size)
        {
            System.Console.WriteLine("Fwd network calculations for : " + SAA_M * sample_size * N + " node-run-sample couples (takes 1-2 minutes)");
            string temp = "";
            SAA_fwd_tree = new string[N, sample_size, SAA_M];

            for (int m = 0; m < SAA_M; m++)
            {
                for (int r = 0; r < sample_size; r++)
                {
                    for (int i = 0; i < N; i++)
                    {
                        if (SAA_neigh[i, r, m] != null)
                        {
                            temp = i.ToString() + "," + fwd_tree_with_BFS(i, r, m);
                        }
                        else
                        {
                            temp = i.ToString();
                        }

                        SAA_fwd_tree[i, r, m] = temp;
                    }
                }
                System.Console.WriteLine(m);
            }
        }
        public static string fwd_tree_with_BFS(int starting_node, int r, int m) // determine the reachable set by Breadth-first-search for each node - sample couple
        {
            List<int> temp_nodes = new List<int>();
            List<int> visited_nodes = new List<int>();
            int[] node_colors = new int[N];
            int[] node_labels = new int[N];
            int starting_node_ID = node_set[starting_node];
            for (int i = 0; i < N; i++)
            {
                node_colors[i] = 0;
                node_labels[i] = -1;
            }
            int node_index = -1;
            string[] neigh_arr;
            int curr_index = 0;

            temp_nodes.Add(starting_node);
            //visited_nodes.Add(starting_node);

            node_index = starting_node;
            int statint_node_index = starting_node;
            node_colors[node_index] = 1;
            node_labels[node_index] = 0;

            while (temp_nodes.Count != 0)
            {
                node_index = temp_nodes[0];
                if (SAA_neigh[node_index, r, m] != null)
                {
                    neigh_arr = SAA_neigh[node_index, r, m].Split(new char[] { ',' });     //neighbour stringini split edelim
                    foreach (string str in neigh_arr)   //tüm komşuları aktifleştirmeye çalış
                    {
                        curr_index = Convert.ToUInt16(str);
                        if (node_colors[curr_index] == 0)
                        {
                            temp_nodes.Add(curr_index);
                            if (!visited_nodes.Contains(curr_index))
                                visited_nodes.Add(curr_index);
                            node_colors[curr_index] = 1;
                            if (curr_index != statint_node_index && node_labels[curr_index] == -1)
                                node_labels[curr_index] = node_labels[node_index] + 1;
                        }

                    }
                }
                temp_nodes.Remove(temp_nodes[0]);
                node_colors[node_index] = 2;
            }
            StringBuilder builder = new StringBuilder();
            foreach (int node in visited_nodes)
            {
                // Append each int to the StringBuilder overload.
                builder.Append(node).Append(",");
            }
            string result = builder.ToString();
            result = result.TrimEnd(',');

            return result;
        }

        //new version
        public static void determine_network_trees(int sample_size) // Determine the RR set by BFS main function
        {
            System.Console.WriteLine("Reverse Reachable set for : " + SAA_M * sample_size * N + " node-run-sample couples (takes 1-2 minutes)");
            SAA_tree_list = new List<List<List<int>>>();

            List<List<int>> SAA_temp_list = new List<List<int>>();
            recorded_RR = new int[N, sample_size];
            for (int r = 0; r < sample_size; r++)
                for (int i = 0; i < N; i++)
                { x_exist[r, i] = false; }
            int[] tree_size = new int[N];
            node_score = new long[N];
            int[] tree = new int[N];
            //for (int m = 0; m < SAA_M; m++)
            {
                int m = 0;
                //  System.Console.WriteLine("m:" + m);
                for (int r = 0; r < sample_size; r++)
                {
                    //mem = System.GC.GetTotalMemory(true) / 1024 / 1024;
                    //mem = 0;
                    if (r % 5 == 0)
                    {// System.Console.Write("-" + r); System.Console.WriteLine(" | Mem: " + mem + "MB , ts: "+ tree_size.Sum());
                        System.Console.WriteLine("---" + r);
                    }

                    {
                        SAA_tree_list.Add(new List<List<int>>());

                        for (int i = 0; i < N; i++)
                        {
                            SAA_tree_list[r].Add(new List<int>());
                            SAA_tree_list[r][i].Add(i);
                            node_score[i]++;
                            if ((run_MEM == 0) || (run_MEM == 1 && r <= mem_limit))
                                recorded_RR[i, r] = 1;
                            SAA_temp_list.Add(new List<int>());
                            SAA_temp_list[i].Add(i);
                            //x_exist[r, i] = true;
                            if (i % 10000 == 0)
                                System.Console.Write("." + i);
                            //add visited_nodes

                            if (SAA_pred_list[r][i].Count() > 0)
                            {
                                if (run_MEM == 1 && r > mem_limit)
                                {
                                    //SAA_tree_list[r][i].AddRange(BFS_withcount(i, r, m, tree, SAA_pred_list, SAA_tree_list));
                                    SAA_temp_list[i].AddRange(BFS_withcount(i, r, m, tree, SAA_pred_list, SAA_temp_list));
                                    tree[i] = 1;
                                }
                                else
                                {
                                    SAA_tree_list[r][i].AddRange(BFS_IM(i, r, m, tree, SAA_pred_list, SAA_tree_list));
                                    tree[i] = 1;
                                }

                                x_exist[r, i] = true;
                            }
                            else
                            {
                                y_obj[i]++;
                            }

                            //tree_size[i] = tree_size[i] + SAA_tree_list[r][i].Count;
                        }
                        SAA_temp_list.Clear();
                        for (int i = 0; i < N; i++)
                            tree[i] = 0;
                    }
                }

                //System.Console.WriteLine(m);
            }
            //Int64 totalsize = tree_size.Sum();
            System.Console.WriteLine("RR Set finished! Size: ");
            //determine_network_trees2(sample_size);

        }

        //new version
        public static void determine_network_trees2(int sample_size) // This one orders with respect to the node_count
        {
            System.Console.WriteLine("Reverse Reachable set for : " + SAA_M * sample_size * N + " node-run-sample couples (takes 1-2 minutes)");
            SAA_tree_list = new List<List<List<int>>>();

            List<List<int>> SAA_temp_list = new List<List<int>>();

            for (int r = 0; r < sample_size; r++)
                for (int i = 0; i < N; i++)
                { x_exist[r, i] = false; }
            int[] tree_size = new int[N];
            node_score = new long[N];
            int[] tree = new int[N];
            //for (int m = 0; m < SAA_M; m++)
            {
                int m = 0;
                List<int> sorted_list = new List<int>();
                for (int i = 0; i < N; i++)
                    sorted_list.Add(i);
                //  System.Console.WriteLine("m:" + m);
                for (int r = 0; r < sample_size; r++)
                {
                    //mem = System.GC.GetTotalMemory(true) / 1024 / 1024;
                    //mem = 0;
                    if (r % 5 == 0)
                    {// System.Console.Write("-" + r); System.Console.WriteLine(" | Mem: " + mem + "MB , ts: "+ tree_size.Sum());
                        System.Console.WriteLine("---" + r);
                    }

                    SAA_tree_list.Add(new List<List<int>>());
                    for (int i = 0; i < N; i++)
                    {
                        SAA_tree_list[r].Add(new List<int>());
                        SAA_temp_list.Add(new List<int>());
                    }


                    foreach (int i in sorted_list)
                    {
                        SAA_tree_list[r][i].Add(i);
                        node_score[i]++;
                        SAA_temp_list[i].Add(i);
                        //x_exist[r, i] = true;
                        if (i % 10000 == 0)
                            System.Console.Write("." + i);
                        //add visited_nodes

                        if (SAA_pred_list[r][i].Count() > 0)
                        {
                            if (theoption == 1)
                            {
                                //SAA_tree_list[r][i].AddRange(BFS_withcount(i, r, m, tree, SAA_pred_list, SAA_tree_list));
                                SAA_temp_list[i].AddRange(BFS_withcount(i, r, m, tree, SAA_pred_list, SAA_temp_list));
                                tree[i] = 1;
                            }
                            else
                            {
                                SAA_tree_list[r][i].AddRange(BFS_IM(i, r, m, tree, SAA_pred_list, SAA_tree_list));
                                tree[i] = 1;
                            }

                            x_exist[r, i] = true;
                        }
                        else
                        {
                            y_obj[i]++;
                        }


                        //tree_size[i] = tree_size[i] + SAA_tree_list[r][i].Count;
                    }
                    SAA_temp_list.Clear();
                    for (int i = 0; i < N; i++)
                        tree[i] = 0;
                    if (r == 0)
                    {
                        Dictionary<int, double> node_score_sorted = new Dictionary<int, double>();
                        for (int ii = 0; ii < N; ii++)
                        {
                            node_score_sorted.Add((int)ii, node_score[ii]);
                        }
                        sorted_list.Clear();
                        foreach (KeyValuePair<int, double> item in node_score_sorted.OrderBy(x => x.Value))
                        {
                            sorted_list.Add(item.Key);
                        };

                    }
                }


                //System.Console.WriteLine(m);
            }
            //Int64 totalsize = tree_size.Sum();
            System.Console.WriteLine("RR Set finished! Size: ");

        }


        public static void determine_network_trees_mem(int sample_size) // Determine the RR set by BFS main function
        {
            double mem = 0;
            memory_sample = new int[N];
            System.Console.WriteLine("Reverse Reachable set for : " + SAA_M * sample_size * N + " node-run-sample couples (takes 1-2 minutes)");
            SAA_tree_list = new List<List<List<int>>>();

            int[] tree_size = new int[N];
            node_score = new long[N];
            int[] tree = new int[N];
            //for (int m = 0; m < SAA_M; m++)
            {
                int m = 0;
                for (int r = 0; r < sample_size; r++)
                    SAA_tree_list.Add(new List<List<int>>());
                //  System.Console.WriteLine("m:" + m);
                for (int i = 0; i < N; i++)
                {
                    //mem = System.GC.GetTotalMemory(true) / 1024 / 1024;
                    //mem = 0;
                    if (i % 1000 == 0)
                    {// System.Console.Write("-" + r); System.Console.WriteLine(" | Mem: " + mem + "MB , ts: "+ tree_size.Sum());
                        System.Console.Write("-" + i);
                    }

                    for (int r = 0; r < sample_size; r++)
                    {
                        x_exist[r, i] = false;
                        SAA_tree_list[r].Add(new List<int>());
                        //SAA_tree_list[r][i].Add(i);
                        node_score[i]++;

                        //add visited_nodes
                        if (SAA_pred_list[r][i].Count() > 0)
                        {
                            List<int> templist = new List<int>();
                            //------------------>>>>templist = BFS_withcount(i, r, m, tree, SAA_pred_list, SAA_tree_list);
                            if (i < mem_limit)
                            {
                                SAA_tree_list[r][i].AddRange(templist); //tree[i] = 1;
                                x_exist[r, i] = true;
                            }
                            //SAA_tree_list[r][i].AddRange(tree_with_BFS(i, r, m, tree));
                        }
                        tree_size[i] = tree_size[i] + SAA_tree_list[r][i].Count;

                    }
                    //for (int i = 0; i < N; i++)
                    //    tree[i] = 0;

                    if (i < mem_limit)
                        memory_sample[i] = 1;
                    else
                        memory_sample[i] = 0;

                }
                //System.Console.WriteLine(m);
            }
            System.Console.WriteLine("RR Set finished!");

        }

        public static void determine_fwd_network_trees_list(int sample_size) // Determine the FR set by BFS main function 
        {
            System.Console.WriteLine("Forward Reachable set for : " + sample_size * N + " node-run-sample couples (takes 1-2 minutes)");
            SAA_fwd_tree_list = new List<List<List<int>>>();
            int[] tree = new int[N];
            //for (int m = 0; m < SAA_M; m++)
            {

                int m = 0;
                //  System.Console.WriteLine("m:" + m);
                for (int r = 0; r < sample_size; r++)
                {
                    if (r % 10 == 0)
                        //System.Console.WriteLine( (ComputerInfo().AvailablePhysicalMemory / 1048576) + "mb free");
                        System.Console.Write("-" + r);
                    SAA_fwd_tree_list.Add(new List<List<int>>());
                    for (int i = 0; i < N; i++)
                    {
                        tree[i] = 1;
                        SAA_fwd_tree_list[r].Add(new List<int>());
                        SAA_fwd_tree_list[r][i].Add(i);

                        //add visited_nodes

                        if (SAA_neigh_list[r][i].Count() > 0)
                        {
                            SAA_fwd_tree_list[r][i].AddRange(BFS(i, r, m, tree, SAA_neigh_list, SAA_fwd_tree_list));
                        }
                    }
                    for (int i = 0; i < N; i++)
                        tree[i] = 0;
                }
                //System.Console.WriteLine(m);

                for (int i = 0; i < N; i++)
                {
                    node_score[i] = 0;
                    for (int r = 0; r < sample_size; r++)
                        node_score[i] = node_score[i] + SAA_fwd_tree_list[r][i].Count;
                }
                m = 0;

            }
        }

        public static List<int> BFS_IM(int starting_node, int r, int m, int[] tree, List<List<List<int>>> neigh, List<List<List<int>>> treelist) // determine the reachable set by Breadth-first-search for each node - sample couple
        {
            var vertices = new Queue<int>();
            vertices.Enqueue(starting_node);

            HashSet<int> visited_nodes = new HashSet<int>();
            bool[] marked = new bool[N];
            while (vertices.Any())
            {
                int curVertex = vertices.Dequeue();
                marked[curVertex] = true;
                foreach (int vertex in neigh[r][curVertex].Where(x => !marked[x]))
                {
                    if (x_exist[r, vertex] == true)
                    {
                        //node_labels[node] = 0;
                        foreach (int nodes in treelist[r][vertex])
                        {
                            visited_nodes.Add(nodes);
                            marked[nodes] = true;
                        }
                    }
                    else
                    {
                        visited_nodes.Add(vertex);
                        vertices.Enqueue(vertex);
                    }

                }
            }

            if (visited_nodes.Contains(starting_node))
            {
                visited_nodes.Remove(starting_node);
            }
            foreach (int node in visited_nodes)
                node_score[node]++;
            return visited_nodes.ToList();
        }

        public static List<int> BFS_IM_simple(int starting_node, int r, int[,] tree, List<List<List<int>>> neigh, List<List<List<int>>> treelist) // determine the reachable set by Breadth-first-search for each node - sample couple
        {
            var vertices = new Queue<int>();
            vertices.Enqueue(starting_node);

            HashSet<int> visited_nodes = new HashSet<int>();
            bool[] marked = new bool[N];
            while (vertices.Any())
            {
                int curVertex = vertices.Dequeue();
                marked[curVertex] = true;
                foreach (int vertex in neigh[r][curVertex].Where(x => !marked[x]))
                {
                    if (tree[r, vertex] == 1)
                    {
                        //node_labels[node] = 0;
                        foreach (int nodes in treelist[r][vertex])
                        {
                            visited_nodes.Add(nodes);
                            marked[nodes] = true;
                        }
                    }
                    else
                    {
                        visited_nodes.Add(vertex);
                        vertices.Enqueue(vertex);
                    }

                }
            }

            if (visited_nodes.Contains(starting_node))
            {
                visited_nodes.Remove(starting_node);
            }
            return visited_nodes.ToList();
        }

        public static List<int> BFS_IM_simple2(int starting_node, int r, int[] tree, List<List<List<int>>> neigh, List<List<int>> treelist) // determine the reachable set by Breadth-first-search for each node - sample couple
        {
            var vertices = new Queue<int>();
            vertices.Enqueue(starting_node);

            HashSet<int> visited_nodes = new HashSet<int>();
            bool[] marked = new bool[N];
            while (vertices.Any())
            {
                int curVertex = vertices.Dequeue();
                marked[curVertex] = true;
                foreach (int vertex in neigh[r][curVertex].Where(x => !marked[x]))
                {
                    if (tree[vertex] == 1)
                    {
                        //node_labels[node] = 0;
                        foreach (int nodes in treelist[vertex])
                        {
                            visited_nodes.Add(nodes);
                            marked[nodes] = true;
                        }
                    }
                    else
                    {
                        visited_nodes.Add(vertex);
                        vertices.Enqueue(vertex);
                    }

                }
            }

            if (visited_nodes.Contains(starting_node))
            {
                visited_nodes.Remove(starting_node);
            }
            return visited_nodes.ToList();
        }

        public static List<int> BFS_withcount(int starting_node, int r, int m, int[] tree, List<List<List<int>>> neigh, List<List<int>> treelist) // determine the reachable set by Breadth-first-search for each node - sample couple
        {
            //Queue<int> temp_nodes = new Queue<int>();
            List<int> temp_nodes = new List<int>();
            HashSet<int> visited_nodes = new HashSet<int>();
            bool[] marked = new bool[N];

            //temp_nodes.Enqueue(starting_node);
            temp_nodes.Add(starting_node);
            //visited_nodes.Add(starting_node);

            int node_index = starting_node;
            int statint_node_index = starting_node;
            marked[node_index] = true;
            //node_labels[node_index] = 0;

            while (temp_nodes.Count != 0)
            {
                //node_index = temp_nodes.Dequeue();
                node_index = temp_nodes[0];
                if (neigh[r][node_index] != null)
                {
                    foreach (int node in neigh[r][node_index].Where(x => !marked[x]))   //tüm komşuları aktifleştirmeye çalış
                    {
                        if (tree[node] == 1)
                        {
                            visited_nodes.Add(node);
                            marked[node] = true;
                            //node_labels[node] = 0;
                            foreach (int nodes in treelist[node])
                            {
                                visited_nodes.Add(nodes);
                                marked[nodes] = true;
                                //node_labels[nodes] = 0;
                                //temp_nodes.Remove(nodes);
                            }
                        }
                        else
                        {
                            //temp_nodes.Enqueue(node);
                            temp_nodes.Add(node);
                            visited_nodes.Add(node);
                            //if (curr_index != statint_node_index && node_labels[node] == -1)
                            //    node_labels[node] = node_labels[node_index] + 1;
                        }

                    }
                }

                temp_nodes.Remove(temp_nodes[0]);
                marked[node_index] = true;
                //node_score[node_index]++;
            }
            if (visited_nodes.Contains(starting_node))
            {
                visited_nodes.Remove(starting_node);
            }
            foreach (int node in visited_nodes)
                node_score[node]++;
            return visited_nodes.ToList();
        }

        public static List<int> BFS(int starting_node, int r, int m, int[] tree, List<List<List<int>>> neigh, List<List<List<int>>> treelist) // determine the reachable set by Breadth-first-search for each node - sample couple
        {
            List<int> temp_nodes = new List<int>();
            HashSet<int> visited_nodes = new HashSet<int>();
            int[] node_colors = new int[N];
            int[] node_labels = new int[N];
            int starting_node_ID = node_set[starting_node];

            for (int i = 0; i < N; i++)
            {
                node_colors[i] = 0;
                node_labels[i] = -1;
            }
            int node_index = -1;
            int curr_index = 0;

            temp_nodes.Add(starting_node);
            //visited_nodes.Add(starting_node);

            node_index = starting_node;
            int statint_node_index = starting_node;
            node_colors[node_index] = 1;
            node_labels[node_index] = 0;

            while (temp_nodes.Count != 0)
            {
                node_index = temp_nodes[0];
                if (neigh[r][node_index] != null)
                {
                    foreach (int node in neigh[r][node_index])   //tüm komşuları aktifleştirmeye çalış
                    {
                        curr_index = (int)node;
                        if (node_colors[curr_index] == 0)
                        {
                            if (tree[curr_index] > 0)
                            {
                                foreach (int nodes in treelist[r][curr_index])
                                {
                                    visited_nodes.Add(nodes);
                                    //node_score[nodes]++;
                                    node_colors[nodes] = 2;
                                    node_labels[nodes] = 0;
                                    //temp_nodes.Remove(nodes);
                                }
                            }
                            else
                            {
                                temp_nodes.Add(curr_index);
                                visited_nodes.Add(curr_index);
                                //node_score[curr_index]++;
                                node_colors[curr_index] = 1;
                                if (curr_index != statint_node_index && node_labels[curr_index] == -1)
                                    node_labels[curr_index] = node_labels[node_index] + 1;
                            }
                        }

                    }
                }
                temp_nodes.Remove(temp_nodes[0]);
                node_colors[node_index] = 2;
            }
            if (visited_nodes.Contains(starting_node))
            {
                visited_nodes.Remove(starting_node);
                //node_score[starting_node]--;
            }
            return visited_nodes.ToList();
        }

        public static List<int> BFS2(int starting_node, int r, int m, List<List<List<int>>> neigh) // determine the reachable set by Breadth-first-search for each node - sample couple
        {
            var vertices = new Queue<int>();
            vertices.Enqueue(starting_node);

            HashSet<int> visited_nodes = new HashSet<int>();
            bool[] marked = new bool[N];
            while (vertices.Any())
            {
                int curVertex = vertices.Dequeue();
                marked[curVertex] = true;
                foreach (int vertex in neigh[r][curVertex].Where(x => !marked[x]))
                {
                    visited_nodes.Add(vertex);
                    vertices.Enqueue(vertex);
                }
            }

            if (visited_nodes.Contains(starting_node))
            {
                visited_nodes.Remove(starting_node);
            }

            return visited_nodes.ToList();
        }

        public static List<int> BFS_TipTop(int starting_node) // BFS for Tiptop
        {
            var vertices = new Queue<int>();
            vertices.Enqueue(starting_node);
            int n_visit_mark = 0;
            Random rnd = new Random();

            HashSet<int> visited_nodes = new HashSet<int>();
            bool[] marked = new bool[N];
            int[] visit_mark = new int[N];
            visit_mark[n_visit_mark++] = starting_node;
            marked[starting_node] = true;
            //marked[curVertex] = true;
            while (vertices.Any())
            {
                int curVertex = vertices.Dequeue();

                for (int i = 0; i < Tiptop_pred_list[curVertex].Count; i++)
                {
                    int item = Tiptop_pred_list[curVertex][i];
                    if (marked[item])
                        continue;
                    else
                    {
                        double temp_arc_weight = rnd.NextDouble();
                        if (temp_arc_weight > Tiptop_w_list[curVertex][i])
                            continue;
                        visit_mark[n_visit_mark++] = item;
                        marked[item] = true;
                        visited_nodes.Add(item);
                    }
                    vertices.Enqueue(item);
                }
            }

            if (visited_nodes.Contains(starting_node))
            {
                visited_nodes.Remove(starting_node);
            }
            foreach (int node in visited_nodes)
                node_score[node]++;
            for (int i = 0; i < n_visit_mark; i++)
                marked[visit_mark[i]] = false;
            return visited_nodes.ToList();
        }

        public static void reduce_tree_list()
        {
            //determine_fwd_network_trees_list(SAA_N1);
            List<int> dominated = new List<int>();
            int count = 0;
            count = countlist(SAA_tree_list);
            int no_of_x_removed = 0;
            for (int i = 0; i < N; i++)
                y_obj[i] = 0;

            for (int i = 0; i < 1; i++)
            {
                //if (SAA_fwd_tree_list[0][i].Count > 10)
                goto gotoloc2;
                y_obj[i] = 0;
                List<int> PL2 = new List<int>();
                PL2.AddRange(SAA_tree_list[0][i]);  //take all predecessors of node i from the first sample
                PL2.Remove(i);
                foreach (int node in PL2.ToList())    // check each predecessor of i one by one, if it exists in pred list of i in all samples
                {
                    for (int r = 1; r < SAA_N1; r++)
                    {
                        //List<int> list_to_check = new List<int>();
                        //list_to_check.AddRange(SAA_fwd_tree_list[r][i]);
                        foreach (int location in SAA_fwd_tree_list[r][i].ToList())
                        {
                            if (SAA_tree_list[r][(int)location].IndexOf(node) < 0)
                            {
                                PL2.Remove(node);
                                //break;
                                goto gotoloc;
                            }
                        }
                    }
                    dominated.Add(i);
                    remove_i_from_list(i);
                    break;
                    gotoloc:;
                }
                gotoloc2:;
            }
            System.Console.WriteLine("Removed: ");
            count = countlist(SAA_tree_list);
            int temp_removed = 0;

            for (int r = 0; r < trial_limit; r++)
            {
                for (int i = 0; i < N; i++)
                {
                    if (SAA_tree_list[r][i].Count == 1)
                    {
                        int thenode = (int)SAA_tree_list[r][i][0];
                        y_obj[thenode] = y_obj[thenode] + 1;
                        remove_constraint(i, thenode, r);
                        no_of_x_removed++;
                    }
                }           //end of for loop for nodes

                //System.Console.Write(no_of_x_removed-temp_removed+"-");
                temp_removed = no_of_x_removed;
            }
            System.Console.WriteLine("Dominated: " + dominated.Count);
            System.Console.WriteLine("no_of_x_removed: " + no_of_x_removed);

            //return dominated;
        }

        public static void remove_i_from_list(int node)
        {
            int thenode = (int)node;
            {
                for (int r = 0; r < SAA_N1; r++)
                {
                    List<int> list_to_check = new List<int>();
                    list_to_check.AddRange(SAA_fwd_tree_list[r][thenode]); // find the locations where node exists
                    foreach (int location in list_to_check.ToList())
                    {
                        SAA_tree_list[r][(int)location].Remove(thenode);    //RR setten sil
                    }
                    SAA_fwd_tree_list[r][thenode].Clear();  //Fwd setten sil
                }
            }
        }

        public static void remove_constraint(int i, int node, int r)
        {
            //double mem = 0;
            //int x=SAA_tree_list[r][i].Count;
            //mem = System.GC.GetTotalMemory(true) ;
            SAA_tree_list[r][i].Clear();
            //mem = System.GC.GetTotalMemory(true);
            //x = SAA_tree_list[r][i].Count;
            SAA_tree_list[r][i] = null;
            //mem = System.GC.GetTotalMemory(true);


            // SAA_fwd_tree_list[r][node].Remove(i);
            x_exist[i, r] = false;

        }

        public static int countlist(List<List<List<int>>> list)
        {
            int count = 0;
            for (int i = 0; i < N; i++)
            {
                for (int r = 0; r < SAA_N1; r++)
                {
                    count = count + list[r][i].Count;
                }
            }
            return count;
        }

        public static double mip_model(int SAA_m, int SAA_type, int sample_size)
        {
            save_model = 0; // to save model.lp file
            save_log2 = 0;  // to save the solution of model

            double influence = 0;
            double influence2 = 0;
            double influence3 = 0;
            double influence4 = 0;

            //influence = (double)construct_model(SAA_m, SAA_type, sample_size);
            Stopwatch st1 = new Stopwatch();

            //influence = model_import(k_init);
            st1.Start();
            if (run_MIP == 1)
            {

                //Gurobi7.5
                //influence = (double)construct_model2_gurobi(SAA_m, SAA_type, sample_size) / sample_size;
                //System.Console.WriteLine(st1.Elapsed);
                st1.Reset();
                //reduce_tree_list();
                st1.Start();
                influence = (double)construct_model2_gurobi(SAA_m, SAA_type, sample_size) / sample_size;

                //influence = (double)construct_model3_gurobi(SAA_m, 1, sample_size) / sample_size;
                //CPLEX
                //influence = (double)construct_model2(SAA_m, SAA_type, sample_size);
                System.Console.WriteLine("Integer sol: " + influence);

                //GRBEnv env = new GRBEnv("mip1.log");
                //GRBModel model = new GRBModel(env);
                //model = new GRBModel(env, "model0.mps");
                //model.Optimize();
                //cplex_model = new Cplex();
                //cplex_model.ImportModel("model0.mps");
                //cplex_model.Solve();
                //influence3 = (double)construct_model2b_gurobi(SAA_m, SAA_type, sample_size) / sample_size;
                //System.Console.WriteLine("Integer-2 sol: " + influence3 + "... act: " + (N - influence3));
                //influence4 = (double)construct_model2_gurobi_kucukyavuz(SAA_m, SAA_type, sample_size) / sample_size;
                System.Console.WriteLine("Kucukyavuz sol: " + influence4);
            }

            if (run_pipage == 1)  // on LP_model function below
            {
                //influence2 = (double)construct_model2_gurobi_LP(SAA_m, SAA_type, sample_size, 0) / sample_size;
                //System.Console.WriteLine("LP sol: " + influence2);
                //influence4 = (double)construct_model2b_LP(SAA_m, SAA_type, sample_size) / sample_size;
                //System.Console.WriteLine("LP-2 sol: " + influence4 + "... act: " + (N - influence4));
            }


            //influence2 = (double)construct_model_pipage_manuel_IP(SAA_m, SAA_type, sample_size) / sample_size; 
            //influence2 = (double)construct_model_pipage_manuel_LP(SAA_m, SAA_type, sample_size) / sample_size;


            //if (influence != influence2)
            //System.Console.ReadKey();
            //influence = (double)gurobi_bipartite(SAA_m, SAA_type, sample_size) / sample_size;

            System.Console.WriteLine(st1.Elapsed);
            st1.Reset();

            //st1.Start();
            //influence2 = (double)construct_model2(SAA_m, SAA_type, sample_size);
            //System.Console.WriteLine(st1.Elapsed);
            //st1.Reset();
            //System.Console.WriteLine("The influence is :" + influence);
            //System.Console.WriteLine("The influence-2 is :" + influence2);
            //swvar.WriteLine("The influence is :" + influence);
            //if (influence != influence2)
            //{
            //    System.Console.WriteLine("inf not equal inf-2");
            //    System.Console.ReadKey();
            //}

            return influence;

            // System.Console.ReadKey();

        }

        public static double LP_model(int SAA_m, int SAA_type, int sample_size)
        {
            save_model = 0; // to save model.lp file
            save_log2 = 0;  // to save the solution of model

            double influence = 0;
            double influence2 = 0;
            double influence3 = 0;
            double influence4 = 0;
            //influence = (double)construct_model(SAA_m, SAA_type, sample_size);
            Stopwatch st1 = new Stopwatch();

            //influence = model_import(k_init);
            st1.Start();

            if (run_pipage == 1)
            {
                influence2 = (double)construct_model2_gurobi_LP(SAA_m, SAA_type, sample_size, 0) / sample_size;
                System.Console.WriteLine("LP sol: " + influence2);
                //influence4 = (double)construct_model2b_LP(SAA_m, SAA_type, sample_size) / sample_size;
                //System.Console.WriteLine("LP-2 sol: " + influence4 + "... act: " + (N - influence4));


            }


            //influence2 = (double)construct_model_pipage_manuel_IP(SAA_m, SAA_type, sample_size) / sample_size; 
            //influence2 = (double)construct_model_pipage_manuel_LP(SAA_m, SAA_type, sample_size) / sample_size;


            //if (influence != influence2)
            //System.Console.ReadKey();
            //influence = (double)gurobi_bipartite(SAA_m, SAA_type, sample_size) / sample_size;

            System.Console.WriteLine(st1.Elapsed);
            st1.Reset();

            //st1.Start();
            //influence2 = (double)construct_model2(SAA_m, SAA_type, sample_size);
            //System.Console.WriteLine(st1.Elapsed);
            //st1.Reset();
            //System.Console.WriteLine("The influence is :" + influence);
            //System.Console.WriteLine("The influence-2 is :" + influence2);
            //swvar.WriteLine("The influence is :" + influence);
            //if (influence != influence2)
            //{
            //    System.Console.WriteLine("inf not equal inf-2");
            //    System.Console.ReadKey();
            //}

            return influence2;

            // System.Console.ReadKey();

        }


        public static double LR_0(int SAA_m, int remove_nodes, int sample_size)
        {
            double solution = 0.0;
            no_of_LR_iter = 0;
            Beta_ir = new double[N, sample_size];
            x_ir = new double[N, sample_size];
            y_i = new double[N];
            double[] c_i = new double[N];
            double[] p_i = new double[N];
            int j = 0;
            double z_UB = 50.0 * BIGM; //min UB
            double z_LB = -50.0 * BIGM;  // feas sol.
            double lambda = 2;
            int[,] gradient = new int[N, sample_size];
            double temp_UB = 0;
            double temp_LB = 0;
            double step_size = 0;
            double stopping_threshold = 0.005;
            int max_no_improvement_limit = 30;
            int LR_continue = 1;
            double z_UB_prev = 0;
            int no_improvement = 0;
            int iterlim = 1500;
            int iter = 1;
            int[,] tree = new int[sample_size, N];
            List<int> y_list = new List<int>();
            List<int> y_iter = new List<int>();
            List<int> y_best = new List<int>();
            List<int> y_toremove = new List<int>();
            List<int> temp_y = new List<int>();
            List<int> y_ever = new List<int>();
            List<List<int>> y_no_good = new List<List<int>>();
            List<List<List<int>>> y_influencees = new List<List<List<int>>>();
            double t1, t2, t3, t4, t5, t6;
            sw.Reset();
            if (fixed_probability > 0.1 || N > 10000)
            {
                iterlim = 750;
                stopping_threshold = 0.009;
                max_no_improvement_limit = 20;
            }
            //sw.Stop(); sw_elapsed = sw.Elapsed; t1 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start();
            //initialize beta_ir
            for (int i = 0; i < N; i++)
            {
                y_iter.Add(i);

                c_i[i] = node_score[i];// + y_obj[i];
                p_i[i] = N * SAA_N1 * 2;        /// FOR Simplified LR
                for (int r = 0; r < sample_size; r++)
                {
                    //Beta_ir[i, r] = LP_duals[i+1]; // initialize with duals
                    //if (x_exist[r, i] == true)
                    Beta_ir[i, r] = 1;
                    tree[r, i] = recorded_RR[i, r];
                }
            }
            System.Console.WriteLine("Finished initialization of LR! SAA" + SAA_m);

            //sw.Stop(); sw_elapsed = sw.Elapsed; t2 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start(); System.Console.WriteLine(t2 / 10000000);

            do
            {
                //int tempctr = 0;
                //stopping_threshold = 0.002;
                for (int i = 0; i < N; i++)
                {
                    //c_i[i] = y_obj[i];        /// FOR Simplified LR
                    y_i[i] = 0;
                    for (int r = 0; r < sample_size; r++)
                    {
                        //if (x_exist[r, i] == true)    /// FOR simplified LR
                        {
                            if (1 - Beta_ir[i, r] > 0)
                            {
                                x_ir[i, r] = 1;
                                temp_UB = temp_UB + 1 - Beta_ir[i, r];
                                //tempctr++;
                            }
                            else
                                x_ir[i, r] = 0;
                        }
                    }
                }
                //System.Console.WriteLine("from x: " + temp_UB);
                //System.Console.WriteLine("Finished Step-1, calculated x_ir");
                // sw.Stop(); sw_elapsed = sw.Elapsed; t3 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start(); System.Console.WriteLine(t3 / 10000000);
                int the_node = 0;

                Dictionary<int, double> c_i_sorted = new Dictionary<int, double>();
                for (int i = 0; i < y_iter.Count; i++)
                {
                    the_node = y_iter[i];
                    c_i_sorted.Add(the_node, c_i[the_node]);
                }

                // algorithmic no good cuts
                if (LR_NG_Cuts == 1)
                {
                    bool continueloop = false;
                    List<int> temp_y_list = new List<int>();
                    do
                    {
                        temp_y_list.Clear();
                        temp_y_list.AddRange(c_i_sorted.OrderByDescending(x => x.Value).Take(k_init).Select(x => x.Key).ToList());

                        foreach (List<int> thelist in y_no_good)
                        {
                            if (!thelist.Except(temp_y_list).Any())
                            {
                                c_i_sorted[temp_y_list[k_init - 1]] = -100000;// * c_i[temp_y_list[k_init - 1]];
                                continueloop = true;
                                break;
                            }
                            else
                            {
                                continueloop = false;
                            }
                        }

                    } while (continueloop);
                }


                foreach (KeyValuePair<int, double> item in c_i_sorted.OrderByDescending(x => x.Value).Take(k_init))
                {
                    y_i[item.Key] = 1;
                    y_list.Add(item.Key);
                    temp_UB = temp_UB + c_i[item.Key];
                };

                if (y_list.All(temp_y.Contains))
                {
                    System.Console.Write("DN");
                }
                else
                {
                    //find a feasible solution
                    List<HashSet<int>> x_list_int = new List<HashSet<int>>();
                    for (int r = 0; r < sample_size; r++)
                    {
                        x_list_int.Add(new HashSet<int>());
                    }

                    for (int i = 0; i < y_list.Count; i++)
                    {
                        //temp_LB = temp_LB + y_obj[y_list[i]]; /// for simplified LR
                        if (y_ever.IndexOf(y_list[i]) > -1)
                        {
                            int the_index = y_ever.IndexOf(y_list[i]);
                            for (int r = 0; r < sample_size; r++)
                            {
                                foreach (int node in y_influencees[the_index][r])   //my predecessors can activate me
                                {
                                    x_list_int[r].Add(node);
                                }
                            }
                        }
                        else
                        {
                            y_ever.Add(y_list[i]);
                            int the_index = y_ever.IndexOf(y_list[i]);
                            y_influencees.Add(new List<List<int>>());

                            for (int r = 0; r < sample_size; r++)
                            {
                                y_influencees[the_index].Add(new List<int>());
                                y_influencees[the_index][r].Add(y_list[i]);
                                x_list_int[r].Add(y_list[i]);
                                List<int> single_list = new List<int>();
                                foreach (int node in BFS2(y_list[i], r, 0, SAA_neigh_list).ToList())
                                {
                                    //if (x_exist[r, node] == true)
                                    {
                                        y_influencees[the_index][r].Add(node);
                                        x_list_int[r].Add(node);
                                    }

                                }
                            }
                        }
                    }
                    temp_LB = temp_LB + x_list_int.Select(x => x.Count).Sum();
                    // You have the y_obj below for the feasible solution if you need uncomment.


                    //for (int i = 0; i < y_list.Count; i++)
                    //{
                    //    int the_index = y_list[i];
                    //    temp_LB = temp_LB + y_obj[the_index];
                    //}
                    //System.Console.WriteLine("Finished Step-3, finding a feasible solution");
                    // sw.Stop(); sw_elapsed = sw.Elapsed; t4 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start(); System.Console.WriteLine(t4 / 10000000);
                }

                if (temp_LB >= z_LB)
                {
                    z_LB = temp_LB;
                    y_best.Clear();
                    for (int jj = 0; jj < y_list.Count; jj++)
                        y_best.Add(y_list[jj]);
                }
                else
                {
                    if (LR_NG_Cuts == 1)
                    {
                        y_no_good.Add(new List<int>());
                        System.Console.Write("No good : ");
                        foreach (int node in y_list)
                        {
                            y_no_good[y_no_good.Count - 1].Add(node);
                            System.Console.Write(node + ",");
                        }
                    }
                }

                if (temp_UB < z_UB)
                {
                    z_UB = temp_UB;
                }

                if (lambda < stopping_threshold || z_LB * (1.0 + stopping_threshold) > z_UB || iter > iterlim)
                {
                    LR_continue = 0;
                }
                double sum_sqr = 0;
                // find nodes to delete
                List<int> y_thisround = new List<int>();
                for (int i = 0; i < N; i++)
                {
                    if (y_i[i] == 1)
                    {
                        //if (p_i[i] > z_UB)
                        //   p_i[i] = z_UB;
                        p_i[i] = Math.Min(p_i[i], z_UB);
                    }

                    else
                    {
                        //if (p_i[i] > z_UB + c_i[i] - c_i[y_list[k_init - 1]])
                        //    p_i[i] = z_UB + c_i[i] - c_i[y_list[k_init - 1]];
                        //if (p_i[i] < z_UB + c_i[i] - c_i[y_list[k_init - 1]])
                        //    p_i[i] = z_UB + c_i[i] - c_i[y_list[k_init - 1]];
                        p_i[i] = Math.Min(p_i[i], z_UB + c_i[i] - c_i[y_list[k_init - 1]]);
                    }

                    if (p_i[i] < z_LB)
                    {
                        if (!y_ever.Contains(i))
                        {
                            if (remove_nodes == 1)
                            {
                                y_iter.Remove(i);

                                if (solution_LR.Contains(";" + node_set[i] + ";"))
                                    c_i[i] = -1 * N;
                                c_i[i] = -1 * N;
                            }
                        }

                        if (!y_toremove.Contains(i))
                        {
                            y_toremove.Add(i);
                            y_thisround.Add(i);
                        }

                        //if (y_best.Contains(i))
                        //System.Console.WriteLine("Alert! " + i);
                    }


                    for (int r = 0; r < sample_size; r++)
                    {
                        gradient[i, r] = 0;
                    }
                }

                for (int i = 0; i < N; i++)
                {
                    for (int r = 0; r < sample_size; r++)
                    {
                        //if (x_exist[r, i] == true)        /// for simplified LR
                        {
                            gradient[i, r] = gradient[i, r] + (int)x_ir[i, r];
                            if (y_i[i] == 1)
                            {
                                int the_index = y_ever.IndexOf(i);
                                foreach (int node in y_influencees[the_index][r].ToList())   //my predecessors can activate me
                                {
                                    //if (x_exist[r, node] == true)       //for simplified LR
                                    gradient[node, r] = gradient[node, r] - 1;
                                }
                            }
                        }
                    }
                }

                for (int i = 0; i < N; i++)
                {
                    for (int r = 0; r < sample_size; r++)
                    {
                        //if (x_exist[r, i] == true)
                        sum_sqr = sum_sqr + gradient[i, r] * gradient[i, r];
                    }
                }
                if (sum_sqr == 0)
                    System.Console.WriteLine("S_SQR=0");
                step_size = lambda * (1.05 * z_UB - z_LB) / sum_sqr;
                //System.Console.WriteLine("Finished Step-4, Calculating gradients & stepsize");
                double beta_new = -1;
                int counter = 0;
                int counter_mem = 0;

                List<List<int>> temp_list = new List<List<int>>();

                for (int r = 0; r < sample_size; r++)
                {
                    int[] temp_tree = new int[N];
                    counter_mem = 0;//System.Console.Write(r + "..");
                    for (int i = 0; i < N; i++)
                    {
                        temp_list.Add(new List<int>());
                        //if (x_exist[r, i] == true)        /// for simplified LR
                        {
                            beta_new = Beta_ir[i, r] + step_size * gradient[i, r];
                            if (beta_new < 0)
                                beta_new = 0;
                            if (beta_new >= 1 && remove_nodes == 0)
                                beta_new = 1;
                            if (beta_new != Beta_ir[i, r])
                            {
                                {
                                    c_i[i] = c_i[i] + beta_new - Beta_ir[i, r]; counter++;
                                    List<int> current_list = new List<int>();
                                    if (tree[r, i] == 0)
                                    {
                                        //if (r <5)
                                        //{
                                        //    SAA_tree_list[r][i].AddRange(BFS_IM_simple(i, r, tree, SAA_pred_list, SAA_tree_list));
                                        //    tree[r, i] = 1;
                                        //    //counter_mem++;
                                        //    current_list.AddRange(SAA_tree_list[r][i]);
                                        //}
                                        //else
                                        {
                                            temp_list[i].Add(i);
                                            temp_list[i].AddRange(BFS_IM_simple2(i, r, temp_tree, SAA_pred_list, temp_list));
                                            temp_tree[i] = 1;
                                            current_list.AddRange(temp_list[i]);
                                        }
                                    }
                                    else
                                    {
                                        current_list.AddRange(SAA_tree_list[r][i]);
                                    }

                                    foreach (int node in current_list.Skip(1).ToList())
                                    {
                                        //if (x_exist[r, node] == true)
                                        c_i[node] = c_i[node] + beta_new - Beta_ir[i, r]; //counter_mem++;
                                    }
                                    counter++; current_list.Clear();
                                }
                                Beta_ir[i, r] = beta_new;
                            }
                        }
                    }
                    temp_list.Clear();
                }

                if (z_UB == z_UB_prev)
                    no_improvement++;

                z_UB_prev = z_UB;
                if (no_improvement >= max_no_improvement_limit)
                {
                    lambda = lambda / 2;
                    no_improvement = 0;
                }

                sw.Stop(); sw_elapsed = sw.Elapsed; t5 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start();
                System.Console.WriteLine(iter + "-> " + z_UB + " --- " + z_LB + " --- " + temp_LB + " - " + (z_UB / z_LB - 1) + " - " + t5 / 10000000 + " // y_count:" + y_iter.Count + "( " + counter + ")..." + string.Join(",", y_list.ToArray()));
                if (lambda < stopping_threshold || z_LB * (1.0 + stopping_threshold) > z_UB || iter > iterlim || (t5 / 10000000) > 3600 || (z_UB - z_LB) < 0.00001)
                {
                    LR_continue = 0;
                    //StreamWriter swt = new StreamWriter("betas");
                    //for (int i = 0; i < N; i++)
                    //{
                    //    for (int r = 0; r < sample_size; r++)
                    //    {
                    //        if (SAA_tree_list[r][i].Count > 0)        /// for simplified LR
                    //        {
                    //            if (Beta_ir[i, r] > 0)
                    //                swt.WriteLine("B_" + i + "_" + r + " : " + Beta_ir[i, r]);
                    //        }
                    //    }
                    //}
                    //swt.Close();
                }
                else
                {
                    temp_y = check_list_equality(y_list, temp_y);
                    y_list.Clear();
                    temp_LB = 0;
                    temp_UB = 0;
                    iter++;
                }
                // sw.Stop(); sw_elapsed = sw.Elapsed; t6 = System.Convert.ToDouble(sw_elapsed.Ticks);
                // sw.Start();
                //if (iter < 20)
                //    LR_continue = 1;
                no_of_LR_iter = iter;
            } while (LR_continue > 0);


            solution = z_LB;
            solution_LR = "";
            for (int i = 0; i < y_best.Count; i++)
            {
                solution_LR = solution_LR + ";" + node_set[y_best[i]];
            }
            solution_LR = solution_LR + ";";
            List<int> tempresult = new List<int>();
            for (int j2 = 0; j2 < y_best.Count; j2++)
            {
                tempresult.Add((int)y_best[j2]);
            }
            SAA_LR_list.Add(tempresult);

            z_LRUB = z_UB / sample_size;

            return solution;
        }


        public static double LR_0_mem(int SAA_m, int remove_nodes, int sample_size)
        {
            double solution = 0.0;
            Beta_ir = new double[N, sample_size];
            x_ir = new double[N, sample_size];
            y_i = new double[N];
            double[] c_i = new double[N];
            double[] p_i = new double[N];
            int j = 0;
            double z_UB = N * sample_size + 1; //min UB
            double z_LB = -1.0 * N * sample_size - 1;  // feas sol.
            double lambda = 2;
            int[,] gradient = new int[N, sample_size];
            double temp_UB = 0;
            double temp_LB = 0;
            double step_size = 0;
            double stopping_threshold = 0.00001;
            int max_no_improvement_limit = 30;
            int LR_continue = 1;
            double z_UB_prev = 0;
            int no_improvement = 0;
            int iterlim = 1500;
            int iter = 1;
            List<int> y_list = new List<int>();
            List<int> y_iter = new List<int>();
            List<int> y_best = new List<int>();
            List<int> y_toremove = new List<int>();
            List<int> temp_y = new List<int>();
            List<int> y_ever = new List<int>();
            List<List<List<int>>> y_influencees = new List<List<List<int>>>();
            double t1, t2, t3, t4, t5, t6;
            sw.Reset();
            //sw.Stop(); sw_elapsed = sw.Elapsed; t1 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start();
            //initialize beta_ir
            for (int i = 0; i < N; i++)
            {
                y_iter.Add(i);
                c_i[i] = node_score[i];
                p_i[i] = N * SAA_N1;        /// FOR Simplified LR
                for (int r = 0; r < sample_size; r++)
                {
                    //Beta_ir[i, r] = LP_duals[i+1]; // initialize with duals
                    //if (x_exist[i, r] == true)
                    Beta_ir[i, r] = 1;
                }
            }
            System.Console.WriteLine("Finished initialization of LR! SAA" + SAA_m);

            //sw.Stop(); sw_elapsed = sw.Elapsed; t2 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start(); System.Console.WriteLine(t2 / 10000000);

            do
            {
                //int tempctr = 0;
                for (int i = 0; i < N; i++)
                {
                    //c_i[i] = y_obj[i];        /// FOR Simplified LR
                    y_i[i] = 0;
                    for (int r = 0; r < sample_size; r++)
                    {
                        //if (x_exist[i, r] == true)    /// FOR simplified LR
                        {
                            if (1 - Beta_ir[i, r] > 0)
                            {
                                x_ir[i, r] = 1;
                                temp_UB = temp_UB + 1 - Beta_ir[i, r];
                                //tempctr++;
                            }
                            else
                                x_ir[i, r] = 0;
                        }
                    }
                }
                //System.Console.WriteLine("Finished Step-1, calculated x_ir");
                // sw.Stop(); sw_elapsed = sw.Elapsed; t3 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start(); System.Console.WriteLine(t3 / 10000000);
                int the_node = 0;
                //for (int i = 0; i < y_iter.Count; i++)
                //{
                //    the_node=y_iter[i];
                //    //if (my_node_set.IndexOf(the_node) !=-1)
                //    for (int r = 0; r < sample_size; r++)
                //    {
                //        foreach (int node in SAA_fwd_tree_list[r][the_node].ToList())   //my predecessors can activate me
                //        {
                //            c_i[the_node] = c_i[the_node] + Beta_ir[node, r];
                //        }
                //    }
                //}
                //System.Console.WriteLine("Finished Step-1b, calculated c_i");
                //sw.Stop(); sw_elapsed = sw.Elapsed; t3 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start(); System.Console.WriteLine(t3 / 10000000);


                Dictionary<int, double> c_i_sorted = new Dictionary<int, double>();
                for (int i = 0; i < y_iter.Count; i++)
                {
                    the_node = y_iter[i];
                    c_i_sorted.Add(the_node, c_i[the_node]);
                }

                foreach (KeyValuePair<int, double> item in c_i_sorted.OrderByDescending(x => x.Value).Take(k_init))
                {
                    y_i[item.Key] = 1;
                    y_list.Add(item.Key);
                    temp_UB = temp_UB + c_i[item.Key];
                };

                if (y_list.All(temp_y.Contains))
                {
                    System.Console.Write("DN");
                }
                else
                {
                    //find a feasible solution
                    List<HashSet<int>> x_list_int = new List<HashSet<int>>();
                    for (int r = 0; r < sample_size; r++)
                    {
                        x_list_int.Add(new HashSet<int>());
                    }

                    for (int i = 0; i < y_list.Count; i++)
                    {
                        //temp_LB = temp_LB + y_obj[y_list[i]]; /// for simplified LR
                        if (y_ever.IndexOf(y_list[i]) > -1)
                        {
                            int the_index = y_ever.IndexOf(y_list[i]);
                            for (int r = 0; r < sample_size; r++)
                            {
                                foreach (int node in y_influencees[the_index][r])   //my predecessors can activate me
                                {
                                    //if (x_exist[node, r] == true)
                                    x_list_int[r].Add(node);
                                }
                            }
                        }
                        else
                        {
                            y_ever.Add(y_list[i]);
                            int the_index = y_ever.IndexOf(y_list[i]);
                            y_influencees.Add(new List<List<int>>());

                            for (int r = 0; r < sample_size; r++)
                            {
                                y_influencees[the_index].Add(new List<int>());
                                y_influencees[the_index][r].Add(y_list[i]);
                                x_list_int[r].Add(y_list[i]);
                                List<int> single_list = new List<int>();
                                foreach (int node in BFS2(y_list[i], r, 0, SAA_neigh_list).ToList())
                                {
                                    y_influencees[the_index][r].Add(node);
                                    x_list_int[r].Add(node);
                                }
                            }
                        }
                    }
                    temp_LB = temp_LB + x_list_int.Select(x => x.Count).Sum();
                    //System.Console.WriteLine("Finished Step-3, finding a feasible solution");
                    // sw.Stop(); sw_elapsed = sw.Elapsed; t4 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start(); System.Console.WriteLine(t4 / 10000000);
                }

                if (temp_LB >= z_LB)
                {
                    z_LB = temp_LB;
                    y_best.Clear();
                    for (int jj = 0; jj < y_list.Count; jj++)
                        y_best.Add(y_list[jj]);
                }
                //else
                //{
                //    List<int> intersect = new List<int>(y_best.Intersect(y_list).ToList());
                //    if (intersect.Count == 0)
                //    {
                //        foreach(int node in y_list)
                //            y_iter.Remove(node);
                //    } 
                //}

                if (temp_UB < z_UB)
                {
                    z_UB = temp_UB;
                }

                if (lambda < stopping_threshold || z_LB * (1.0 + stopping_threshold) > z_UB || iter > iterlim)
                {
                    LR_continue = 0;
                }
                double sum_sqr = 0;
                // find nodes to delete
                List<int> y_thisround = new List<int>();
                for (int i = 0; i < N; i++)
                {
                    if (y_i[i] == 1)
                    {
                        if (p_i[i] > z_UB)
                            p_i[i] = z_UB;
                    }

                    else
                    {
                        if (p_i[i] > z_UB + c_i[i] - c_i[y_list[k_init - 1]])
                            p_i[i] = z_UB + c_i[i] - c_i[y_list[k_init - 1]];
                    }

                    if (p_i[i] < z_LB)
                    {
                        if (!y_best.Contains(i))
                        {
                            if (remove_nodes == 1)
                                //y_iter.Remove(i);
                                c_i[i] = -1 * N;
                        }

                        if (!y_toremove.Contains(i))
                        {
                            y_toremove.Add(i);
                            y_thisround.Add(i);
                        }

                        //if (y_best.Contains(i))
                        //System.Console.WriteLine("Alert! " + i);
                    }


                    for (int r = 0; r < sample_size; r++)
                    {
                        gradient[i, r] = 0;
                    }
                }

                for (int i = 0; i < N; i++)
                {
                    for (int r = 0; r < sample_size; r++)
                    {
                        //if (SAA_tree_list[r][i].Count > 0)        /// for simplified LR
                        {
                            gradient[i, r] = gradient[i, r] + (int)x_ir[i, r];
                            if (y_i[i] == 1)
                            {
                                int the_index = y_ever.IndexOf(i);
                                foreach (int node in y_influencees[the_index][r].ToList())   //my predecessors can activate me
                                {
                                    //if (x_exist[node, r] == true)       //for simplified LR
                                    gradient[node, r] = gradient[node, r] - 1;
                                }
                            }
                        }
                    }
                }

                for (int i = 0; i < N; i++)
                {
                    for (int r = 0; r < sample_size; r++)
                    {
                        sum_sqr = sum_sqr + gradient[i, r] * gradient[i, r];
                    }
                }

                step_size = lambda * (1.05 * z_UB - z_LB) / sum_sqr;
                //System.Console.WriteLine("Finished Step-4, Calculating gradients & stepsize");
                double beta_new = -1; int counter = 0; int counter2 = 0;
                for (int i = 0; i < N; i++)
                {//if (i % 100 == 0)
                 //     System.Console.Write(i);
                    for (int r = 0; r < sample_size; r++)
                    {
                        //if (x_exist[i, r] == true)        /// for simplified LR
                        {
                            beta_new = Beta_ir[i, r] + step_size * gradient[i, r];
                            if (beta_new < 0)
                                beta_new = 0;
                            if (beta_new >= 1)
                                beta_new = 1;
                            if (beta_new != Beta_ir[i, r])
                            {
                                counter++;
                                c_i[i] = c_i[i] + beta_new - Beta_ir[i, r];
                                if (x_exist[r, i] == false)
                                {
                                    if (SAA_pred_list[r][i].Count() > 0)
                                    {
                                        List<int> templist = BFS2(i, r, 0, SAA_pred_list).ToList();
                                        foreach (int node in templist)
                                        {
                                            c_i[node] = c_i[node] + beta_new - Beta_ir[i, r];
                                        }
                                        if (y_list.Contains(i))
                                        {
                                            SAA_tree_list[r][i].AddRange(templist); counter2++;
                                            x_exist[r, i] = true;
                                        }
                                    }
                                }
                                else
                                {
                                    foreach (int node in SAA_tree_list[r][i].ToList())
                                    {
                                        c_i[node] = c_i[node] + beta_new - Beta_ir[i, r];
                                    }
                                }

                                Beta_ir[i, r] = beta_new;
                            }
                        }
                    }
                }

                if (z_UB == z_UB_prev)
                    no_improvement++;

                z_UB_prev = z_UB;
                if (no_improvement >= max_no_improvement_limit)
                {
                    lambda = lambda / 2;
                    no_improvement = 0;
                }

                sw.Stop(); sw_elapsed = sw.Elapsed; t5 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start();
                System.Console.WriteLine(iter + "-> " + z_UB + " --- " + z_LB + " --- " + temp_LB + " - " + (z_UB / z_LB - 1) + " - " + t5 / 10000000 + " // y_count:" + y_iter.Count + "( " + counter + "/" + counter2 + ")..." + string.Join(",", y_list.ToArray()));
                if (lambda < stopping_threshold || z_LB * (1.0 + stopping_threshold) > z_UB || iter > iterlim || (t5 / 10000000) > 3600 || (z_UB - z_LB) < 1)
                {
                    LR_continue = 0;
                    //StreamWriter swt = new StreamWriter("betas");
                    //for (int i = 0; i < N; i++)
                    //{
                    //    for (int r = 0; r < sample_size; r++)
                    //    {
                    //        if (SAA_tree_list[r][i].Count > 0)        /// for simplified LR
                    //        {
                    //            if (Beta_ir[i, r] > 0)
                    //                swt.WriteLine("B_" + i + "_" + r + " : " + Beta_ir[i, r]);
                    //        }
                    //    }
                    //}
                    //swt.Close();
                }
                else
                {
                    temp_y = check_list_equality(y_list, temp_y);
                    y_list.Clear();
                    temp_LB = 0;
                    temp_UB = 0;
                    iter++;
                }
                // sw.Stop(); sw_elapsed = sw.Elapsed; t6 = System.Convert.ToDouble(sw_elapsed.Ticks);
                // sw.Start();
            } while (LR_continue > 0);


            solution = z_LB;
            solution_LR = "";
            for (int i = 0; i < y_best.Count; i++)
            {
                solution_LR = solution_LR + ";" + node_set[y_best[i]];
            }

            List<int> tempresult = new List<int>();
            for (int j2 = 0; j2 < y_best.Count; j2++)
            {
                tempresult.Add((int)y_best[j2]);
            }
            SAA_LR_list.Add(tempresult);

            z_LRUB = z_UB / sample_size;

            return solution;
        }



        public static double LR_Tiptop(int SAA_m, int remove_nodes, int sample_size)
        {
            double solution = 0.0;
            no_of_LR_iter = 0;
            double[] Beta_r = new double[sample_size];
            double[] x_r = new double[sample_size];
            y_i = new double[N];
            double[] c_i = new double[N];
            double[] p_i = new double[N];
            int j = 0;
            double z_UB = 50.0 * BIGM; //min UB
            double z_LB = -50.0 * BIGM;  // feas sol.
            double lambda = 2;
            int[] gradient = new int[sample_size];
            double temp_UB = 0;
            double temp_LB = 0;
            double step_size = 0;
            double stopping_threshold = 0.00005;
            int max_no_improvement_limit = 30;
            int LR_continue = 1;
            double z_UB_prev = 0;
            int no_improvement = 0;
            int iterlim = 1500;
            int iter = 1;
            int[,] tree = new int[sample_size, N];
            List<int> y_list = new List<int>();
            List<int> y_iter = new List<int>();
            List<int> y_best = new List<int>();
            List<int> y_toremove = new List<int>();
            List<int> temp_y = new List<int>();
            List<int> y_ever = new List<int>();
            List<List<int>> y_no_good = new List<List<int>>();
            List<HashSet<int>> y_influencees = new List<HashSet<int>>();
            double t1, t2, t3, t4, t5, t6;
            sw.Reset();
            if (fixed_probability > 0.1 || N > 10000)
            {
                iterlim = 1000;
                stopping_threshold = 0.001;
                max_no_improvement_limit = 30;
            }
            //sw.Stop(); sw_elapsed = sw.Elapsed; t1 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start();
            //initialize beta_ir
            for (int i = 0; i < N; i++)
            {
                y_iter.Add(i);

                c_i[i] = node_score[i] + y_obj[i];
                p_i[i] = N * SAA_N1 * 2;        /// FOR Simplified LR
            }

            for (int r = 0; r < sample_size; r++)
            {
                Beta_r[r] = 1;
            }
            System.Console.WriteLine("Finished initialization of LR! SAA" + SAA_m);

            //sw.Stop(); sw_elapsed = sw.Elapsed; t2 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start(); System.Console.WriteLine(t2 / 10000000);

            do
            {
                //int tempctr = 0;
                //stopping_threshold = 0.002;
                for (int i = 0; i < N; i++)
                {
                    //c_i[i] = y_obj[i];        /// FOR Simplified LR
                    y_i[i] = 0;
                }

                for (int r = 0; r < sample_size; r++)
                {
                    //if (x_exist[r, i] == true)    /// FOR simplified LR
                    {
                        if (1 - Beta_r[r] > 0)
                        {
                            x_r[r] = 1;
                            temp_UB = temp_UB + 1 - Beta_r[r];
                            //tempctr++;
                        }
                        else
                            x_r[r] = 0;
                    }
                }
                //System.Console.WriteLine("from x: " + temp_UB);
                //System.Console.WriteLine("Finished Step-1, calculated x_ir");
                // sw.Stop(); sw_elapsed = sw.Elapsed; t3 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start(); System.Console.WriteLine(t3 / 10000000);
                int the_node = 0;

                Dictionary<int, double> c_i_sorted = new Dictionary<int, double>();
                for (int i = 0; i < y_iter.Count; i++)
                {
                    the_node = y_iter[i];
                    c_i_sorted.Add(the_node, c_i[the_node]);
                }

                // algorithmic no good cuts
                //if (LR_NG_Cuts == 1)
                //{
                //    bool continueloop = false;
                //    List<int> temp_y_list = new List<int>();
                //    do
                //    {
                //        temp_y_list.Clear();
                //        temp_y_list.AddRange(c_i_sorted.OrderByDescending(x => x.Value).Take(k_init).Select(x => x.Key).ToList());

                //        foreach (List<int> thelist in y_no_good)
                //        {
                //            if (!thelist.Except(temp_y_list).Any())
                //            {
                //                c_i_sorted[temp_y_list[k_init - 1]] = -100000;// * c_i[temp_y_list[k_init - 1]];
                //                continueloop = true;
                //                break;
                //            }
                //            else
                //            {
                //                continueloop = false;
                //            }
                //        }

                //    } while (continueloop);
                //}


                foreach (KeyValuePair<int, double> item in c_i_sorted.OrderByDescending(x => x.Value).Take(k_init))
                {
                    y_i[item.Key] = 1;
                    y_list.Add(item.Key);
                    temp_UB = temp_UB + c_i[item.Key];
                };

                if (y_list.All(temp_y.Contains))
                {
                    System.Console.Write("DN");
                }
                else
                {
                    //find a feasible solution
                    HashSet<int> x_list_int = new HashSet<int>();

                    for (int i = 0; i < y_list.Count; i++)
                    {
                        //temp_LB = temp_LB + y_obj[y_list[i]]; /// for simplified LR
                        if (y_ever.IndexOf(y_list[i]) > -1)
                        {
                            int the_index = y_ever.IndexOf(y_list[i]);

                            foreach (int node in y_influencees[the_index])   //my predecessors can activate me
                            {
                                x_list_int.Add(node);
                            }
                        }
                        else
                        {
                            y_ever.Add(y_list[i]);
                            int the_index = y_ever.IndexOf(y_list[i]);
                            y_influencees.Add(new HashSet<int>());

                            //for (int r = 0; r < sample_size; r++)
                            {
                                //y_influencees[the_index].Add(new List<int>());
                                //y_influencees[the_index].Add(y_list[i]);
                                //x_list_int.Add(y_list[i]);
                                var single_list = hypernodes.Select((x, v) => new { x, v }).Where(a => a.x.IndexOf(y_list[i]) >= 0).Select(a => a.v).ToList();
                                foreach (var node in single_list)
                                {
                                    //if (x_exist[r, node] == true)
                                    {
                                        y_influencees[the_index].Add(Convert.ToUInt16(node));
                                        x_list_int.Add(Convert.ToUInt16(node));
                                    }

                                }
                            }
                        }
                    }
                    temp_LB = temp_LB + x_list_int.Count;
                    // You have the y_obj below for the feasible solution if you need uncomment.


                    for (int i = 0; i < y_list.Count; i++)
                    {
                        int the_index = y_list[i];
                        temp_LB = temp_LB + y_obj[the_index];
                    }
                    //System.Console.WriteLine("Finished Step-3, finding a feasible solution");
                    // sw.Stop(); sw_elapsed = sw.Elapsed; t4 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start(); System.Console.WriteLine(t4 / 10000000);
                }

                if (temp_LB >= z_LB)
                {
                    z_LB = temp_LB;
                    y_best.Clear();
                    for (int jj = 0; jj < y_list.Count; jj++)
                        y_best.Add(y_list[jj]);
                }
                else
                {
                    if (LR_NG_Cuts == 1)
                    {
                        y_no_good.Add(new List<int>());
                        System.Console.Write("No good : ");
                        foreach (int node in y_list)
                        {
                            y_no_good[y_no_good.Count - 1].Add(node);
                            System.Console.Write(node + ",");
                        }
                    }
                }

                if (temp_UB < z_UB)
                {
                    z_UB = temp_UB;
                }

                if (lambda < stopping_threshold || z_LB * (1.0 + stopping_threshold) > z_UB || iter > iterlim)
                {
                    LR_continue = 0;
                }
                double sum_sqr = 0;
                // find nodes to delete
                List<int> y_thisround = new List<int>();

                for (int r = 0; r < sample_size; r++)
                {
                    gradient[r] = 0;
                }

                for (int r = 0; r < sample_size; r++)
                {
                    gradient[r] = gradient[r] + (int)x_r[r];
                }

                foreach (int y_elmnt in y_list)
                {
                    int the_index = y_ever.IndexOf(y_elmnt);
                    foreach (int node in y_influencees[the_index].ToList())   //my predecessors can activate me
                    {
                        //if (x_exist[r, node] == true)       //for simplified LR
                        gradient[node] = gradient[node] - 1;
                    }
                }

                for (int r = 0; r < sample_size; r++)
                {
                    //if (x_exist[r, i] == true)
                    sum_sqr = sum_sqr + gradient[r] * gradient[r];
                }
                if (sum_sqr == 0)
                    System.Console.WriteLine("S_SQR=0");
                step_size = lambda * (1.05 * z_UB - z_LB) / sum_sqr;
                //System.Console.WriteLine("Finished Step-4, Calculating gradients & stepsize");
                double beta_new = -1;
                int counter = 0;
                int counter_mem = 0;

                List<List<int>> temp_list = new List<List<int>>();

                for (int r = 0; r < sample_size; r++)
                {
                    int[] temp_tree = new int[N];
                    counter_mem = 0;//System.Console.Write(r + "..");

                    temp_list.Add(new List<int>());
                    //if (x_exist[r, i] == true)        /// for simplified LR
                    {
                        beta_new = Beta_r[r] + step_size * gradient[r];
                        if (beta_new < 0)
                            beta_new = 0;
                        if (beta_new >= 1 && remove_nodes == 0)
                            beta_new = 1;
                        if (beta_new != Beta_r[r])
                        {
                            foreach (int node in hypernodes[r].ToList())
                            {
                                c_i[node] = c_i[node] + beta_new - Beta_r[r]; //counter_mem++;
                            }
                            counter++;

                            Beta_r[r] = beta_new;
                        }
                    }

                    temp_list.Clear();
                }

                if (z_UB == z_UB_prev)
                    no_improvement++;

                z_UB_prev = z_UB;
                if (no_improvement >= max_no_improvement_limit)
                {
                    lambda = lambda / 2;
                    no_improvement = 0;
                }

                sw.Stop(); sw_elapsed = sw.Elapsed; t5 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start();
                System.Console.WriteLine(iter + "-> " + z_UB + " --- " + z_LB + " --- " + temp_LB + " - " + (z_UB / z_LB - 1) + " - " + t5 / 10000000 + " // y_count:" + y_iter.Count + "( " + counter + ")..." + string.Join(",", y_list.ToArray()));
                if (lambda < stopping_threshold || z_LB * (1.0 + stopping_threshold) > z_UB || iter > iterlim || (t5 / 10000000) > 3600 || (z_UB - z_LB) < 0.00001)
                {
                    LR_continue = 0;
                    //StreamWriter swt = new StreamWriter("betas");
                    //for (int i = 0; i < N; i++)
                    //{
                    //    for (int r = 0; r < sample_size; r++)
                    //    {
                    //        if (SAA_tree_list[r][i].Count > 0)        /// for simplified LR
                    //        {
                    //            if (Beta_ir[i, r] > 0)
                    //                swt.WriteLine("B_" + i + "_" + r + " : " + Beta_ir[i, r]);
                    //        }
                    //    }
                    //}
                    //swt.Close();
                }
                else
                {
                    temp_y = check_list_equality(y_list, temp_y);
                    y_list.Clear();
                    temp_LB = 0;
                    temp_UB = 0;
                    iter++;
                }
                // sw.Stop(); sw_elapsed = sw.Elapsed; t6 = System.Convert.ToDouble(sw_elapsed.Ticks);
                // sw.Start();
                //if (iter < 20)
                //    LR_continue = 1;
                no_of_LR_iter = iter;
            } while (LR_continue > 0);


            solution = z_LB;
            solution_LR = "";
            for (int i = 0; i < y_best.Count; i++)
            {
                solution_LR = solution_LR + ";" + node_set[y_best[i]];
            }
            solution_LR = solution_LR + ";";
            List<int> tempresult = new List<int>();
            for (int j2 = 0; j2 < y_best.Count; j2++)
            {
                tempresult.Add((int)y_best[j2]);
            }
            SAA_LR_list.Add(tempresult);

            z_LRUB = z_UB;

            return solution;
        }


        public static double LR_1(int SAA_m, int remove_nodes, int sample_size)
        {
            double solution = 0.0;
            Beta_ir = new double[N, sample_size];
            x_ir = new double[N, sample_size];
            y_i = new double[N];
            double[] c_i = new double[N];
            double[] p_i = new double[N];
            int j = 0;
            double z_UB = 1.0 * BIGM; //min UB
            double z_LB = -1.0 * BIGM;  // feas sol.
            double lambda = 2;
            int[,] gradient = new int[N, sample_size];
            double temp_UB = 0;
            double temp_LB = 0;
            double step_size = 0;
            double stopping_threshold = 0.00001;
            int max_no_improvement_limit = 25;
            int LR_continue = 1;
            double z_UB_prev = 0;
            int no_improvement = 0;
            int iterlim = 1000;
            int iter = 1;
            List<int> y_list = new List<int>();
            List<int> y_iter = new List<int>();
            List<int> y_best = new List<int>();
            List<int> y_toremove = new List<int>();
            List<int> temp_y = new List<int>();
            List<int> y_ever = new List<int>();
            List<List<List<int>>> y_influencees = new List<List<List<int>>>();
            double t1, t2, t3, t4, t5, t6;
            sw.Reset();
            //sw.Stop(); sw_elapsed = sw.Elapsed; t1 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start();
            //initialize beta_ir
            for (int i = 0; i < N; i++)
            {
                y_iter.Add(i);
                c_i[i] = node_score[i];
                p_i[i] = N * SAA_N1;        /// FOR Simplified LR
                for (int r = 0; r < sample_size; r++)
                {
                    //Beta_ir[i, r] = LP_duals[i+1]; // initialize with duals
                    if (x_exist[r, i] == true)
                        Beta_ir[i, r] = 1;
                }
            }
            System.Console.WriteLine("Finished initialization of LR! SAA" + SAA_m);

            //sw.Stop(); sw_elapsed = sw.Elapsed; t2 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start(); System.Console.WriteLine(t2 / 10000000);

            do
            {
                //int tempctr = 0;
                for (int i = 0; i < N; i++)
                {
                    //c_i[i] = y_obj[i];        /// FOR Simplified LR
                    y_i[i] = 0;
                    for (int r = 0; r < sample_size; r++)
                    {
                        if (x_exist[r, i] == true)    /// FOR simplified LR
                        {
                            if (1 - Beta_ir[i, r] > 0)
                            {
                                x_ir[i, r] = 1;
                                temp_UB = temp_UB + 1 - Beta_ir[i, r];
                                //tempctr++;
                            }
                            else
                                x_ir[i, r] = 0;
                        }
                    }
                }
                //System.Console.WriteLine("Finished Step-1, calculated x_ir");
                // sw.Stop(); sw_elapsed = sw.Elapsed; t3 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start(); System.Console.WriteLine(t3 / 10000000);
                int the_node = 0;
                //for (int i = 0; i < y_iter.Count; i++)
                //{
                //    the_node=y_iter[i];
                //    //if (my_node_set.IndexOf(the_node) !=-1)
                //    for (int r = 0; r < sample_size; r++)
                //    {
                //        foreach (int node in SAA_fwd_tree_list[r][the_node].ToList())   //my predecessors can activate me
                //        {
                //            c_i[the_node] = c_i[the_node] + Beta_ir[node, r];
                //        }
                //    }
                //}
                //System.Console.WriteLine("Finished Step-1b, calculated c_i");
                //sw.Stop(); sw_elapsed = sw.Elapsed; t3 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start(); System.Console.WriteLine(t3 / 10000000);


                Dictionary<int, double> c_i_sorted = new Dictionary<int, double>();
                for (int i = 0; i < y_iter.Count; i++)
                {
                    the_node = y_iter[i];
                    c_i_sorted.Add(the_node, c_i[the_node]);
                }

                foreach (KeyValuePair<int, double> item in c_i_sorted.OrderByDescending(x => x.Value).Take(k_init))
                {
                    y_i[item.Key] = 1;
                    y_list.Add(item.Key);
                    temp_UB = temp_UB + c_i[item.Key];
                };

                if (y_list.All(temp_y.Contains))
                {
                    System.Console.Write("DN");
                }
                else
                {
                    //find a feasible solution
                    List<HashSet<int>> x_list_int = new List<HashSet<int>>();
                    for (int r = 0; r < sample_size; r++)
                    {
                        x_list_int.Add(new HashSet<int>());
                    }

                    for (int i = 0; i < y_list.Count; i++)
                    {
                        //temp_LB = temp_LB + y_obj[y_list[i]]; /// for simplified LR
                        if (y_ever.IndexOf(y_list[i]) > -1)
                        {
                            int the_index = y_ever.IndexOf(y_list[i]);
                            for (int r = 0; r < sample_size; r++)
                            {
                                foreach (int node in y_influencees[the_index][r])   //my predecessors can activate me
                                {
                                    //if (x_exist[node, r] == true)
                                    x_list_int[r].Add(node);
                                }
                            }
                        }
                        else
                        {
                            y_ever.Add(y_list[i]);
                            int the_index = y_ever.IndexOf(y_list[i]);
                            y_influencees.Add(new List<List<int>>());

                            for (int r = 0; r < sample_size; r++)
                            {
                                y_influencees[the_index].Add(new List<int>());
                                y_influencees[the_index][r].Add(y_list[i]);
                                x_list_int[r].Add(y_list[i]);
                                List<int> single_list = new List<int>();
                                foreach (int node in BFS2(y_list[i], r, 0, SAA_neigh_list).ToList())
                                {
                                    y_influencees[the_index][r].Add(node);
                                    x_list_int[r].Add(node);
                                }
                            }
                        }
                    }
                    temp_LB = temp_LB + x_list_int.Select(x => x.Count).Sum();
                    //System.Console.WriteLine("Finished Step-3, finding a feasible solution");
                    // sw.Stop(); sw_elapsed = sw.Elapsed; t4 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start(); System.Console.WriteLine(t4 / 10000000);
                }

                if (temp_LB > z_LB)
                {
                    z_LB = temp_LB;
                    y_best.Clear();
                    for (int jj = 0; jj < y_list.Count; jj++)
                        y_best.Add(y_list[jj]);
                }

                if (temp_UB < z_UB)
                {
                    z_UB = temp_UB;
                }

                if (lambda < stopping_threshold || z_LB * (1.0 + stopping_threshold) > z_UB || iter > iterlim)
                {
                    LR_continue = 0;
                }
                double sum_sqr = 0;
                // find nodes to delete
                List<int> y_thisround = new List<int>();
                for (int i = 0; i < N; i++)
                {
                    if (y_i[i] == 1)
                    {
                        if (p_i[i] > z_UB)
                            p_i[i] = z_UB;
                    }

                    else
                    {
                        if (p_i[i] > z_UB + c_i[i] - c_i[y_list[k_init - 1]])
                            p_i[i] = z_UB + c_i[i] - c_i[y_list[k_init - 1]];
                    }

                    if (p_i[i] < z_LB)
                    {
                        if (!y_best.Contains(i))
                        {
                            if (remove_nodes == 1)
                                y_iter.Remove(i);
                        }

                        if (!y_toremove.Contains(i))
                        {
                            y_toremove.Add(i);
                            y_thisround.Add(i);
                        }

                        //if (y_best.Contains(i))
                        //System.Console.WriteLine("Alert! " + i);
                    }


                    for (int r = 0; r < sample_size; r++)
                    {
                        gradient[i, r] = 0;
                    }
                }

                for (int i = 0; i < N; i++)
                {
                    for (int r = 0; r < sample_size; r++)
                    {
                        if (x_exist[r, i] == true)       /// for simplified LR
                        {
                            gradient[i, r] = gradient[i, r] + (int)x_ir[i, r];
                            if (y_i[i] == 1)
                            {
                                int the_index = y_ever.IndexOf(i);
                                foreach (int node in y_influencees[the_index][r].ToList())   //my predecessors can activate me
                                {
                                    if (x_exist[r, node] == true)       //for simplified LR
                                        gradient[node, r] = gradient[node, r] - 1;
                                }
                            }
                        }
                    }
                }

                for (int i = 0; i < N; i++)
                {
                    for (int r = 0; r < sample_size; r++)
                    {
                        sum_sqr = sum_sqr + gradient[i, r] * gradient[i, r];
                    }
                }

                step_size = lambda * (1.05 * z_UB - z_LB) / sum_sqr;
                //System.Console.WriteLine("Finished Step-4, Calculating gradients & stepsize");
                double beta_new = -1;
                for (int i = 0; i < N; i++)
                {
                    for (int r = 0; r < sample_size; r++)
                    {
                        if (x_exist[r, i] == true)        /// for simplified LR
                        {
                            beta_new = Beta_ir[i, r] + step_size * gradient[i, r];
                            if (beta_new < 0)
                                beta_new = 0;
                            if (beta_new >= 1)
                                beta_new = 1;
                            if (beta_new != Beta_ir[i, r])
                            {
                                foreach (int node in SAA_tree_list[r][i].ToList())
                                {
                                    c_i[node] = c_i[node] + beta_new - Beta_ir[i, r];
                                }
                                Beta_ir[i, r] = beta_new;
                            }
                        }
                    }
                }

                if (z_UB == z_UB_prev)
                    no_improvement++;

                z_UB_prev = z_UB;
                if (no_improvement >= max_no_improvement_limit)
                {
                    lambda = lambda / 2;
                    no_improvement = 0;
                }

                sw.Stop(); sw_elapsed = sw.Elapsed; t5 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start();
                System.Console.WriteLine(iter + "-> " + z_UB + " --- " + z_LB + " --- " + temp_LB + " - " + (z_UB / z_LB - 1) + " - " + t5 / 10000000 + " // y_count:" + y_iter.Count + "..." + string.Join(",", y_list.ToArray()));
                if (lambda < stopping_threshold || z_LB * (1.0 + stopping_threshold) > z_UB || iter > iterlim || (t5 / 10000000) > 3600 || (z_UB - z_LB) < 1)
                {
                    LR_continue = 0;
                    //StreamWriter swt = new StreamWriter("betas");
                    //for (int i = 0; i < N; i++)
                    //{
                    //    for (int r = 0; r < sample_size; r++)
                    //    {
                    //        if (SAA_tree_list[r][i].Count > 0)        /// for simplified LR
                    //        {
                    //            if (Beta_ir[i, r] > 0)
                    //                swt.WriteLine("B_" + i + "_" + r + " : " + Beta_ir[i, r]);
                    //        }
                    //    }
                    //}
                    //swt.Close();
                }
                else
                {
                    temp_y = check_list_equality(y_list, temp_y);
                    y_list.Clear();
                    temp_LB = 0;
                    temp_UB = 0;
                    iter++;
                }
                // sw.Stop(); sw_elapsed = sw.Elapsed; t6 = System.Convert.ToDouble(sw_elapsed.Ticks);
                // sw.Start();
            } while (LR_continue > 0);


            solution = z_LB;
            solution_LR = "";
            for (int i = 0; i < y_best.Count; i++)
            {
                solution_LR = solution_LR + ";" + node_set[y_best[i]];
            }

            List<int> tempresult = new List<int>();
            for (int j2 = 0; j2 < y_best.Count; j2++)
            {
                tempresult.Add((int)y_best[j2]);
            }
            SAA_LR_list.Add(tempresult);

            z_LRUB = z_UB / sample_size;

            return solution;
        }

        public static double LR_2(int SAA_m, int SAA_type, int sample_size)
        {
            double solution = 0.0;
            Beta_ir = new double[N, sample_size];
            int[,] LR_x_ir = new int[N, sample_size];
            int[,] y_ir = new int[N, sample_size];
            int[] v_i = new int[N];

            int j = 0;
            double z_UB = 1.0 * BIGM; //min UB
            double z_LB = -1.0 * BIGM;  // feas sol.
            double lambda = 2;
            double[,] gradient = new double[N, sample_size];
            double temp_UB = 0;
            double temp_LB = 0;
            double step_size = 0;
            double stopping_threshold = 0.005;
            int max_no_improvement_limit = 20;
            int LR_continue = 1;
            double z_UB_prev = 0;
            double[] obj_R = new double[sample_size];
            double[] y_avg = new double[N];
            int no_improvement = 0;
            int iter = 1;
            List<int> y_list = new List<int>();
            List<int> y_best = new List<int>();
            List<int> temp_y = new List<int>();

            double t1, t2, t3, t4, t5, t6;
            //sw.Stop(); sw_elapsed = sw.Elapsed; t1 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start();
            //initialize beta_ir
            for (int i = 0; i < N; i++)
            {
                for (int r = 0; r < sample_size; r++)
                {
                    //Beta_ir[i, r] = LP_duals[i+1]; // initialize with duals
                    Beta_ir[i, r] = 0;
                }
            }
            System.Console.WriteLine("Finished initialization of LR!");

            //sw.Stop(); sw_elapsed = sw.Elapsed; t2 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start();
            List<int> temp_list = new List<int>();
            do
            {
                for (int i = 0; i < N; i++)
                {
                    y_list.Add(0);
                    y_avg[i] = 0;
                    for (int r = 0; r < sample_size; r++)
                    {
                        y_ir[i, r] = 0;
                    }
                }

                for (int r = 0; r < sample_size; r++)
                {
                    System.Console.WriteLine("Constructing the " + r + "-th sub-MIP with Gurobi...");
                    try
                    {
                        GRBEnv env = new GRBEnv("mip1.log");
                        GRBModel model = new GRBModel(env);
                        //model.Parameters.Presolve = 1;
                        model.Parameters.OutputFlag = 0;


                        //GRBVar x=new GRBVar;
                        GRBVar[] var_y_ir = new GRBVar[N];
                        GRBVar[] var_x_ir = new GRBVar[N];

                        System.Console.WriteLine("Creating y_i");
                        for (int i = 0; i < N; i++)
                        {
                            var_y_ir[i] = model.AddVar(0.0, 1.0, y_obj[i] - Beta_ir[i, r], GRB.BINARY, "y_" + i + "_" + r);
                        }

                        model.ModelSense = GRB.MAXIMIZE;

                        //----------------------------------------------------------
                        //--------------- create the constraints
                        int counter = 0;
                        GRBLinExpr temp_exp2;
                        temp_exp2 = 0.0;
                        System.Console.WriteLine("Starting the constraints... Total : " + (trial_limit + 1) + " constraints");
                        // exactly k initial active users
                        for (int i = 0; i < N; i++)
                        {
                            temp_exp2.AddTerm(1.0, var_y_ir[i]);
                        }
                        model.AddConstr(temp_exp2 == k_init, "constraint_y");

                        GRBLinExpr temp_exp;

                        temp_exp = 0.0;

                        for (int i = 0; i < N; i++)
                        {
                            if (SAA_tree_list[r][i].Count > 0)
                            {
                                var_x_ir[i] = model.AddVar(0.0, 1.0, 1.0, GRB.CONTINUOUS, "x_" + i + "_" + r);
                                temp_exp.AddTerm(1.0, var_x_ir[i]);

                                foreach (int node in SAA_tree_list[r][i])   //my predecessors can activate me
                                {
                                    {
                                        temp_exp.AddTerm(-1, var_y_ir[(int)node]);
                                    }
                                }
                                model.AddConstr(temp_exp <= 0, "constraint" + (counter + 1) + "_" + r);
                                counter++;
                            }       //end of if for null neighbourhood
                            temp_exp = 0.0;
                        }

                        //model.Write("modelGRB_LR_2" + SAA_m + "r" + r + ".lp");
                        //GRBModel p = model.Presolve();
                        //p.Write("presolve.lp");
                        model.Optimize();

                        if (model.Status == GRB.Status.OPTIMAL)
                        {
                            Console.WriteLine("Obj: " + model.Get(GRB.DoubleAttr.ObjVal));
                            solution = model.Get(GRB.DoubleAttr.ObjVal);

                            for (int jj = 0; jj < N; ++jj)
                            {

                                if (var_y_ir[jj].X > 0.001)
                                {
                                    //result_set.Add(node_set[jj]);
                                    System.Console.WriteLine(var_y_ir[jj].VarName + "=" + var_y_ir[jj].X);
                                    y_ir[jj, r] = (int)var_y_ir[jj].X;
                                    y_avg[jj] = y_avg[jj] + y_ir[jj, r] * 1.0 / sample_size;
                                    y_list[jj]++;
                                }
                            }
                        }
                        else
                        {
                            Console.WriteLine("No solution");
                            solution = 0;
                        }
                        obj_R[r] = solution;
                        model.Dispose();
                        env.Dispose();
                    }
                    catch (GRBException e)
                    {
                        Console.WriteLine("Error code: " + e.ErrorCode + ". " + e.Message);
                    }

                    temp_UB = temp_UB + solution;
                }

                double sum_beta_r = 0;
                for (int i = 0; i < N; i++)
                {

                    for (int r = 0; r < sample_size; r++)
                    {
                        sum_beta_r = sum_beta_r + Beta_ir[i, r];
                    }
                    if (sum_beta_r > 0)
                    {
                        temp_UB = temp_UB + sum_beta_r;
                        v_i[i] = 1;
                    }
                    else
                        v_i[i] = 0;
                    sum_beta_r = 0;
                }

                //find a feasible solution
                Dictionary<int, double> y_sorted = new Dictionary<int, double>();
                for (int i = 0; i < N; i++)
                {
                    y_sorted.Add(i, y_list[i]);
                }

                List<int> y_selected = new List<int>();
                foreach (KeyValuePair<int, double> item in y_sorted.OrderByDescending(x => x.Value).Take(k_init))
                {
                    //y_i[item.Key] = 1;
                    y_selected.Add(item.Key);
                };




                List<List<int>> x_list_int = new List<List<int>>();
                for (int r = 0; r < sample_size; r++)
                {
                    x_list_int.Add(new List<int>());
                }

                for (int i = 0; i < y_selected.Count; i++)
                {
                    temp_LB = temp_LB + y_obj[y_selected[i]]; /// for simplified LR
                    for (int r = 0; r < sample_size; r++)
                    {
                        {
                            //temp_list = SAA_fwd_tree_list[r][y_selected[i]];
                            //neigh_arr = SAA_fwd_tree[y_list[i], r, SAA_m].Split(new char[] { ',' });
                            foreach (int node in temp_list)   //my predecessors can activate me
                            {
                                if (!x_list_int[r].Contains(node))
                                    x_list_int[r].Add(node);
                            }
                        }
                    }

                }
                temp_LB = temp_LB + x_list_int.Select(x => x.Count).Sum();
                //System.Console.WriteLine("Finished Step-3, finding a feasible solution");
                // sw.Stop(); sw_elapsed = sw.Elapsed; t4 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start();
                if (temp_LB > z_LB)
                {
                    z_LB = temp_LB;
                    y_best.Clear();
                    for (int jj = 0; jj < y_selected.Count; jj++)
                        y_best.Add(y_selected[jj]);
                }

                if (temp_UB < z_UB)
                {
                    z_UB = temp_UB;
                }

                if (lambda < stopping_threshold || z_LB * (1.0 + stopping_threshold) > z_UB || iter > 400)
                {
                    LR_continue = 0;
                }
                double sum_sqr = 0;

                // evaluate gradients
                for (int i = 0; i < N; i++)
                {
                    for (int r = 0; r < sample_size; r++)
                    {
                        gradient[i, r] = y_ir[i, r] - v_i[i];
                        //gradient[i, r] = y_ir[i, r] - y_avg[i];
                        sum_sqr = sum_sqr + gradient[i, r] * gradient[i, r];
                        //Beta_ir[i, r] = 0;
                    }
                }
                if (sum_sqr == 0)
                    step_size = 1;
                step_size = lambda * (1.05 * z_UB - z_LB) / sum_sqr;
                //System.Console.WriteLine("Finished Step-4, Calculating gradients & stepsize");
                //sw.Stop(); sw_elapsed = sw.Elapsed; t5 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start();
                for (int i = 0; i < N; i++)
                {
                    for (int r = 0; r < sample_size; r++)
                    {
                        {
                            Beta_ir[i, r] = Beta_ir[i, r] + step_size * gradient[i, r];
                        }
                    }
                }

                if (z_UB == z_UB_prev)
                    no_improvement++;

                z_UB_prev = z_UB;
                if (no_improvement >= max_no_improvement_limit)
                {
                    lambda = lambda / 2;
                    no_improvement = 0;
                }
                System.Console.WriteLine(iter + "-> " + z_UB + " --- " + z_LB + " --- " + temp_UB + " / " + temp_LB + " - " + (z_UB / z_LB - 1));
                if (lambda < stopping_threshold || z_LB * (1.0 + stopping_threshold) > z_UB || iter > 400)
                {
                    LR_continue = 0;
                }
                else
                {
                    //temp_y = check_list_equality(y_list, temp_y);
                    y_list.Clear();
                    temp_LB = 0;
                    temp_UB = 0;
                    iter++;
                }
                // sw.Stop(); sw_elapsed = sw.Elapsed; t6 = System.Convert.ToDouble(sw_elapsed.Ticks);
                // sw.Start();
            } while (LR_continue > 0);


            solution = z_LB;
            solution_LR = "";
            for (int i = 0; i < y_best.Count; i++)
            {
                solution_LR = solution_LR + ";" + node_set[y_best[i]];
            }

            List<int> tempresult = new List<int>();
            for (int j2 = 0; j2 < y_best.Count; j2++)
            {
                tempresult.Add((int)y_best[j2]);
            }
            SAA_LR_list.Add(tempresult);

            z_LRUB = z_UB / sample_size;

            return solution;
        }


        public static double LR_3_Shabbir(int SAA_m, int SAA_type, int sample_size)
        {
            double solution = 0.0;
            Beta_ir = new double[N, sample_size];
            int[,] LR_x_ir = new int[N, sample_size];
            int[,] y_ir = new int[N, sample_size];
            int[] v_i = new int[N];

            int j = 0;
            double z_UB = 1.0 * BIGM; //min UB
            double z_LB = -1.0 * BIGM;  // feas sol.
            double lambda = 2;
            double[,] gradient = new double[N, sample_size];
            double temp_UB = 0;
            double temp_LB = 0;
            double step_size = 0;
            double stopping_threshold = 0.005;
            int max_no_improvement_limit = 20;
            int LR_continue = 1;
            double z_UB_prev = 0;
            double[] obj_R = new double[sample_size];
            double[] y_avg = new double[N];
            int no_improvement = 0;
            int iter = 1;
            List<int> y_list = new List<int>();
            List<int> y_best = new List<int>();
            List<int> temp_y = new List<int>();
            List<List<int>> y_cuts = new List<List<int>>();

            double t1, t2, t3, t4, t5, t6;
            //sw.Stop(); sw_elapsed = sw.Elapsed; t1 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start();
            //initialize beta_ir
            for (int i = 0; i < N; i++)
            {
                for (int r = 0; r < sample_size; r++)
                {
                    //Beta_ir[i, r] = LP_duals[i+1]; // initialize with duals
                    Beta_ir[i, r] = 0;
                }
            }
            System.Console.WriteLine("Finished initialization of LR!");

            //sw.Stop(); sw_elapsed = sw.Elapsed; t2 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start();
            List<int> temp_list = new List<int>();
            do
            {
                for (int i = 0; i < N; i++)
                {
                    y_list.Add(0);
                    y_avg[i] = 0;
                    for (int r = 0; r < sample_size; r++)
                    {
                        y_ir[i, r] = 0;
                    }
                }

                for (int r = 0; r < sample_size; r++)
                {
                    System.Console.WriteLine("Constructing the " + r + "-th sub-MIP with Gurobi...");
                    try
                    {
                        GRBEnv env = new GRBEnv("mip1.log");
                        GRBModel model = new GRBModel(env);
                        //model.Parameters.Presolve = 1;
                        //model.Parameters.OutputFlag = 0;


                        //GRBVar x=new GRBVar;
                        GRBVar[] var_y_ir = new GRBVar[N];
                        GRBVar[] var_x_ir = new GRBVar[N];

                        System.Console.WriteLine("Creating y_i");
                        for (int i = 0; i < N; i++)
                        {
                            var_y_ir[i] = model.AddVar(0.0, 1.0, y_obj[i] - Beta_ir[i, r], GRB.BINARY, "y_" + i + "_" + r);
                        }

                        model.ModelSense = GRB.MAXIMIZE;

                        //----------------------------------------------------------
                        //--------------- create the constraints
                        int counter = 0;
                        GRBLinExpr temp_exp2;
                        temp_exp2 = 0.0;
                        System.Console.WriteLine("Starting the constraints... Total : " + (trial_limit + 1) + " constraints");
                        // exactly k initial active users
                        for (int i = 0; i < N; i++)
                        {
                            temp_exp2.AddTerm(1.0, var_y_ir[i]);
                        }
                        model.AddConstr(temp_exp2 == k_init, "constraint_y");

                        GRBLinExpr temp_exp;

                        temp_exp = 0.0;

                        for (int i = 0; i < N; i++)
                        {
                            if (SAA_tree_list[r][i].Count > 0)
                            {
                                var_x_ir[i] = model.AddVar(0.0, 1.0, 1.0, GRB.CONTINUOUS, "x_" + i + "_" + r);
                                temp_exp.AddTerm(1.0, var_x_ir[i]);

                                foreach (int node in SAA_tree_list[r][i])   //my predecessors can activate me
                                {
                                    {
                                        temp_exp.AddTerm(-1, var_y_ir[(int)node]);
                                    }
                                }
                                model.AddConstr(temp_exp <= 0, "constraint" + (counter + 1) + "_" + r);
                                counter++;
                            }       //end of if for null neighbourhood
                            temp_exp = 0.0;
                        }

                        for (int i = 0; i < y_cuts.Count; i++)
                        {
                            for (int jj = 0; jj < N; jj++)
                            {
                                temp_exp.AddTerm(1.0, var_y_ir[jj]);
                            }
                            foreach (int item in y_cuts[i])
                            {
                                temp_exp.AddTerm(-2.0, var_y_ir[item]);
                            }
                            model.AddConstr(temp_exp >= -1 * (k_init - 1), "constraint_cut" + i + "_" + r);
                            temp_exp = 0.0;
                        }


                        //model.Write("modelGRB_LR_2" + SAA_m + "r" + r + ".lp");
                        //GRBModel p = model.Presolve();
                        //p.Write("presolve.lp");
                        model.Optimize();

                        if (model.Status == GRB.Status.OPTIMAL)
                        {
                            Console.WriteLine("Obj: " + model.Get(GRB.DoubleAttr.ObjVal));
                            solution = model.Get(GRB.DoubleAttr.ObjVal);

                            for (int jj = 0; jj < N; ++jj)
                            {

                                if (var_y_ir[jj].X > 0.001)
                                {
                                    //result_set.Add(node_set[jj]);
                                    System.Console.WriteLine(var_y_ir[jj].VarName + "=" + var_y_ir[jj].X);
                                    y_ir[jj, r] = (int)var_y_ir[jj].X;
                                    y_avg[jj] = y_avg[jj] + y_ir[jj, r] * 1.0 / sample_size;
                                    y_list[jj]++;
                                }
                            }
                        }
                        else
                        {
                            Console.WriteLine("No solution");
                            solution = 0;
                        }
                        obj_R[r] = solution;
                        model.Dispose();
                        env.Dispose();
                    }
                    catch (GRBException e)
                    {
                        Console.WriteLine("Error code: " + e.ErrorCode + ". " + e.Message);
                    }

                    temp_UB = temp_UB + solution;
                }

                double sum_beta_r = 0;
                for (int i = 0; i < N; i++)
                {

                    for (int r = 0; r < sample_size; r++)
                    {
                        sum_beta_r = sum_beta_r + Beta_ir[i, r];
                    }
                    if (sum_beta_r > 0)
                    {
                        temp_UB = temp_UB + sum_beta_r;
                        v_i[i] = 1;
                    }
                    else
                        v_i[i] = 0;
                    sum_beta_r = 0;
                }

                //find a feasible solution
                Dictionary<int, double> y_sorted = new Dictionary<int, double>();
                for (int i = 0; i < N; i++)
                {
                    y_sorted.Add(i, y_list[i]);
                }

                List<int> y_selected = new List<int>();
                foreach (KeyValuePair<int, double> item in y_sorted.OrderByDescending(x => x.Value).Take(k_init))
                {
                    //y_i[item.Key] = 1;
                    y_selected.Add(item.Key);
                };

                y_cuts.Add(y_selected);


                List<List<int>> x_list_int = new List<List<int>>();
                for (int r = 0; r < sample_size; r++)
                {
                    x_list_int.Add(new List<int>());
                }

                for (int i = 0; i < y_selected.Count; i++)
                {
                    temp_LB = temp_LB + y_obj[y_selected[i]]; /// for simplified LR
                    for (int r = 0; r < sample_size; r++)
                    {
                        {
                            //Burayı açmayı unutma uint16 //temp_list = SAA_fwd_tree_list[r][y_selected[i]];
                            //neigh_arr = SAA_fwd_tree[y_list[i], r, SAA_m].Split(new char[] { ',' });
                            foreach (int node in temp_list)   //my predecessors can activate me
                            {
                                if (!x_list_int[r].Contains(node))
                                    x_list_int[r].Add(node);
                            }
                        }
                    }

                }
                temp_LB = temp_LB + x_list_int.Select(x => x.Count).Sum();
                //System.Console.WriteLine("Finished Step-3, finding a feasible solution");
                // sw.Stop(); sw_elapsed = sw.Elapsed; t4 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start();
                if (temp_LB > z_LB)
                {
                    z_LB = temp_LB;
                    y_best.Clear();
                    for (int jj = 0; jj < y_selected.Count; jj++)
                        y_best.Add(y_selected[jj]);
                }

                if (temp_UB < z_UB)
                {
                    z_UB = temp_UB;
                }

                if (lambda < stopping_threshold || z_LB * (1.0 + stopping_threshold) > z_UB || iter > 400)
                {
                    LR_continue = 0;
                }
                double sum_sqr = 0;

                // evaluate gradients
                for (int i = 0; i < N; i++)
                {
                    for (int r = 0; r < sample_size; r++)
                    {
                        gradient[i, r] = y_ir[i, r] - v_i[i];
                        //gradient[i, r] = y_ir[i, r] - y_avg[i];
                        sum_sqr = sum_sqr + gradient[i, r] * gradient[i, r];
                        //Beta_ir[i, r] = 0;
                    }
                }
                if (sum_sqr == 0)
                    step_size = 1;
                step_size = lambda * (1.05 * z_UB - z_LB) / sum_sqr;
                //System.Console.WriteLine("Finished Step-4, Calculating gradients & stepsize");
                //sw.Stop(); sw_elapsed = sw.Elapsed; t5 = System.Convert.ToDouble(sw_elapsed.Ticks); sw.Start();
                for (int i = 0; i < N; i++)
                {
                    for (int r = 0; r < sample_size; r++)
                    {
                        {
                            Beta_ir[i, r] = Beta_ir[i, r] + step_size * gradient[i, r];
                        }
                    }
                }

                if (z_UB == z_UB_prev)
                    no_improvement++;

                z_UB_prev = z_UB;
                if (no_improvement >= max_no_improvement_limit)
                {
                    lambda = lambda / 2;
                    no_improvement = 0;
                }
                System.Console.WriteLine(iter + "-> " + z_UB + " --- " + z_LB + " --- " + temp_UB + " / " + temp_LB + " - " + (z_UB / z_LB - 1));
                if (lambda < stopping_threshold || z_LB * (1.0 + stopping_threshold) > z_UB || iter > 400)
                {
                    LR_continue = 0;
                }
                else
                {
                    //temp_y = check_list_equality(y_list, temp_y);
                    y_list.Clear();
                    temp_LB = 0;
                    temp_UB = 0;
                    iter++;
                }
                // sw.Stop(); sw_elapsed = sw.Elapsed; t6 = System.Convert.ToDouble(sw_elapsed.Ticks);
                // sw.Start();
            } while (LR_continue > 0);


            solution = z_LB;
            solution_LR = "";
            for (int i = 0; i < y_best.Count; i++)
            {
                solution_LR = solution_LR + ";" + node_set[y_best[i]];
            }

            List<int> tempresult = new List<int>();
            System.Console.WriteLine("LR sol.:" + solution_LR);
            for (int j2 = 0; j2 < y_best.Count; j2++)
            {
                tempresult.Add((int)y_best[j2]);
            }
            SAA_LR_list.Add(tempresult);

            z_LRUB = z_UB / sample_size;

            return solution;
        }


        public static List<int> check_list_equality(List<int> y_list, List<int> temp_y)
        {
            var a = y_list.All(temp_y.Contains) && y_list.Count == temp_y.Count;
            if (a != true)
            {
                temp_y.Clear();
                temp_y.AddRange(y_list);
            }
            return temp_y;
        }


        //#region Cplex

        //public static double construct_model(int SAA_m, int SAA_type, int sample_size)  //model with x_irt
        //{
        //    int LP_relaxation = 1;
        //    determine_network_depth(sample_size);
        //    trial_limit = sample_size;
        //    System.Console.WriteLine("Constructing the MIP...");
        //    cplex_model = new Cplex();
        //    IObjective obj = cplex_model.AddMaximize();
        //    lp_model = cplex_model.LPMatrix();

        //    //LP-relaxation-1
        //    //INumVar varx;
        //    //INumVar vary;
        //    //INumExpr[] expr_y = new INumExpr[N];
        //    //INumExpr[, ,] expr_x_lp = new INumExpr[N, trial_limit, SAA_max_network_depth[SAA_m] + 1];
        //    //INumVar[] vary_arr;
        //    //INumVar[] varx_arr;
        //    //vary_arr = new IIntVar[N];
        //    //varx_arr = new IIntVar[N * trial_limit + SAA_total_network_depth[SAA_m]];

        //    //Integer-1
        //    IIntVar varx_int;
        //    IIntVar vary_int;
        //    IIntExpr[] expr_y_int = new IIntExpr[N];
        //    INumExpr[,,] expr_x = new INumExpr[N, trial_limit, SAA_max_network_depth[0] + 1];
        //    IIntVar[] vary_int_arr;
        //    IIntVar[] varx_int_arr;
        //    vary_int_arr = new IIntVar[N];
        //    varx_int_arr = new IIntVar[N * trial_limit + SAA_total_network_depth[0]];

        //    // create the variables
        //    // First create y_i  ( a total of N=# of nodes in the network variables
        //    System.Console.WriteLine("Creating y_i");

        //    for (int i = 0; i < N; i++)
        //    {
        //        //LP-2
        //        //    vary = newColumn_init(cplex_model, obj, 1, 0);
        //        //   vary.Name = "y" + node_set[i];
        //        //  vary_arr[i] = vary;
        //        //  expr_y[i] = vary;
        //        //lp_model.AddColumn(vary);

        //        //Integer-2
        //        vary_int = newColumn_init_integer(cplex_model, obj, 0, 0);
        //        vary_int.Name = "y" + node_set[i];
        //        vary_int_arr[i] = vary_int;
        //        expr_y_int[i] = vary_int;
        //        //lp_model.AddColumn(vary_int);
        //    }
        //    //Lp-3
        //    //lp_model.AddCols(vary_arr); // using the array version of adding columns

        //    //Int-3
        //    lp_model.AddCols(vary_int_arr); // using the array version of adding columns

        //    System.Console.WriteLine("Creating x_irt");
        //    //Next create x_irt ... the variables representing activation of a node-i in monte carlo run-r at the cascade step-t

        //    int counter = 0;
        //    for (int r = 0; r < trial_limit; r++)
        //    {
        //        for (int i = 0; i < N; i++)
        //        {
        //            for (int t = 0; t < network_depth[i, r, 0] + 1; t++)
        //            {
        //                //LP-4
        //                // varx = newColumn_init(cplex_model, obj, 1, 0);
        //                //  varx.Name = "x" + (node_set[i]) + "_" + (r + 1) + "_" + (t);
        //                // varx_arr[counter] = varx;
        //                ////lp_model.AddColumn(varx);
        //                //  expr_x_lp[i, r, t] = varx;

        //                //int-4
        //                varx_int = newColumn_init_integer(cplex_model, obj, 1, 0);
        //                varx_int.Name = "x" + (node_set[i]) + "_" + (r + 1) + "_" + (t);
        //                varx_int_arr[counter] = varx_int;
        //                //lp_model.AddColumn(varx_int);
        //                expr_x[i, r, t] = varx_int;


        //                counter++;
        //            }
        //        }
        //    }
        //    //Lp-5
        //    //lp_model.AddCols(varx_arr); // using the array version of adding columns

        //    //Int-5
        //    lp_model.AddCols(varx_int_arr); // using the array version of adding columns

        //    //----------------------------------------------------------
        //    //--------------- create the constraints
        //    INumExpr temp_exp = null;
        //    IRange rngy;
        //    IRange[] rng_arr;


        //    System.Console.WriteLine("Starting the constraints... Total : " + (3 * trial_limit * N + SAA_total_network_depth[0] + 1) + " constraints");
        //    // exactly k initial active users
        //    for (int i = 0; i < N; i++)
        //    {
        //        if (i == 0)
        //        {
        //            //lp-6
        //            //temp_exp = cplex_model.Prod(recruitment_cost[i], expr_y[i]);
        //            ////temp_exp = expr_y[i];

        //            //int-6
        //            temp_exp = cplex_model.Prod(recruitment_cost[i], expr_y_int[i]);
        //            //temp_exp = expr_y_int[i];
        //        }
        //        else
        //        {
        //            //lp-7
        //            //temp_exp = cplex_model.Sum(temp_exp, cplex_model.Prod(recruitment_cost[i], expr_y[i]));
        //            ////temp_exp = cplex_model.Sum(temp_exp, expr_y[i]);

        //            //int-7
        //            temp_exp = cplex_model.Sum(temp_exp, cplex_model.Prod(recruitment_cost[i], expr_y_int[i]));
        //            //temp_exp = cplex_model.Sum(temp_exp, expr_y_int[i]);
        //        }
        //    }

        //    //rngy = cplex_model.AddEq(k_init, temp_exp);
        //    rngy = cplex_model.AddGe(BUDGET, temp_exp);
        //    lp_model.AddRow(rngy);

        //    //--- influence constraints x_i_r_0 <= y_0                    (total of N.R constraints)
        //    //---- and                  x_i_r_t <= SUM_{j} (x_j_r_t-1)    (total of N.R+total_network_depth constraints)
        //    //---- and                  SUM_{t} x_i_r_t = 1               (total of N.R constraints)
        //    string[] neigh_arr;

        //    temp_exp = cplex_model.NumExpr();
        //    INumExpr temp_exp2 = cplex_model.NumExpr();
        //    rng_arr = new IRange[3 * trial_limit * N + SAA_total_network_depth[0]];
        //    int j = 0;
        //    counter = 0;

        //    for (int r = 0; r < trial_limit; r++)
        //    {
        //        for (int i = 0; i < N; i++)
        //        {
        //            //lp-8
        //            //temp_exp = cplex_model.Prod(-1, expr_x_lp[i, r, 0]);
        //            //temp_exp = cplex_model.Sum(temp_exp, expr_y[i]);
        //            //temp_exp2 = expr_x_lp[i, r, 0];

        //            //int-8
        //            temp_exp = cplex_model.Prod(-1, expr_x[i, r, 0]);
        //            temp_exp = cplex_model.Sum(temp_exp, expr_y_int[i]);
        //            temp_exp2 = expr_x[i, r, 0];


        //            rngy = cplex_model.AddLe(0, temp_exp);
        //            rng_arr[counter] = rngy;
        //            counter++;


        //            // now add the neighbours with x_j terms

        //            if (SAA_pred_list[r][i] != null)
        //            {

        //                for (int jj = 1; jj < network_depth[i, r, 0] + 1; jj++)
        //                {
        //                    //lp-9
        //                    //temp_exp = cplex_model.Prod(-1, expr_x_lp[i, r, jj]);
        //                    //temp_exp2 = cplex_model.Sum(temp_exp2, expr_x_lp[i, r, jj]);
        //                    //int-9
        //                    temp_exp = cplex_model.Prod(-1, expr_x[i, r, jj]);
        //                    temp_exp2 = cplex_model.Sum(temp_exp2, expr_x[i, r, jj]);


        //                    foreach (int node in SAA_pred_list[r][i])   //my predecessors can activate me
        //                    {
        //                        //j_index = Convert.ToUInt16(str);   // convert the selected predecessor to int
        //                        //j = node_set.IndexOf(j_index);
        //                        j = (int)node;
        //                        if (network_depth[j, r, 0] >= jj - 1)
        //                        {
        //                            //lp-10
        //                            //temp_exp = cplex_model.Sum(temp_exp, expr_x_lp[j, r, jj - 1]);

        //                            //int-10
        //                            temp_exp = cplex_model.Sum(temp_exp, expr_x[j, r, jj - 1]);
        //                        }
        //                    }
        //                    rngy = cplex_model.AddLe(0, temp_exp);
        //                    rng_arr[counter] = rngy;
        //                    counter++;
        //                }
        //                rngy = cplex_model.AddGe(1, temp_exp2);
        //                rng_arr[counter] = rngy;
        //                counter++;
        //            }       //end of if for null neighbourhood
        //        }           //end of for loop for nodes
        //    }               //end of for loop for sample size R

        //    // manual cover inequalities
        //    int add_cuts = 0;
        //    /*
        //    if(add_cuts==1)
        //    {
        //        temp_exp = cplex_model.Sum(expr_y[11], expr_y[19], expr_y[21]);
        //        rngy = cplex_model.AddGe(2, temp_exp);
        //        temp_exp = cplex_model.Sum(expr_y[11], expr_y[19], expr_y[20]);
        //        rngy = cplex_model.AddGe(2, temp_exp);
        //        temp_exp = cplex_model.Sum(expr_y[11], expr_y[19], expr_y[10]);
        //        rngy = cplex_model.AddGe(2, temp_exp);
        //        temp_exp = cplex_model.Sum(expr_y[11], expr_y[19], expr_y[8]);
        //        rngy = cplex_model.AddGe(2, temp_exp);
        //        temp_exp = cplex_model.Sum(expr_y[11], expr_y[19], expr_y[22]);
        //        rngy = cplex_model.AddGe(2, temp_exp);
        //        temp_exp = cplex_model.Sum(expr_y[11], expr_y[19], expr_y[16]);
        //        rngy = cplex_model.AddGe(2, temp_exp);
        //    }*/

        //    // fixing some variables
        //    if (SAA_type == 1)
        //    {
        //        for (int i = 0; i < N; i++)
        //        {
        //            //lp-11
        //            //temp_exp = expr_y[i];

        //            //int-11
        //            temp_exp = expr_y_int[i];
        //            if (SAA_current_list.Contains((int)i))
        //            {
        //                rngy = cplex_model.AddEq(1, temp_exp);
        //            }
        //            else
        //            {
        //                rngy = cplex_model.AddEq(0, temp_exp);
        //            }
        //        }

        //    }
        //    //IRange[] rng_arr_new = new IRange[counter];
        //    //for (int t = 0; t < counter; t++)
        //    //    rng_arr_new[t] = rng_arr[t];

        //    //lp_model.AddRows(rng_arr_new);

        //    //if (save_model == 1)
        //    {
        //        cplex_model.ExportModel("modelCPLEX" + SAA_m + ".lp");
        //    }
        //    double solution = -1;
        //    solution = cplex_solve(cplex_model, SAA_m) / trial_limit;
        //    lp_model.Clear();
        //    cplex_model.End();
        //    swvar.WriteLine("Sample-" + SAA_m);
        //    return solution;
        //}

        //public static double construct_model2(int SAA_m, int SAA_type, int sample_size) // simplified model with x_ir
        //{
        //    trial_limit = sample_size;
        //    System.Console.WriteLine("Using CPLEX... Constructing the MIP...");
        //    cplex_model = new Cplex();
        //    IObjective obj = cplex_model.AddMaximize();
        //    lp_model = cplex_model.LPMatrix();

        //    //Integer-1
        //    IIntVar varx_int;
        //    IIntVar vary_int;
        //    IIntExpr[] expr_y_int = new IIntExpr[N];
        //    INumExpr[,] expr_x = new INumExpr[N, trial_limit];
        //    IIntVar[] vary_int_arr;
        //    IIntVar[] varx_int_arr;
        //    vary_int_arr = new IIntVar[N];
        //    varx_int_arr = new IIntVar[N * trial_limit];

        //    // create the variables
        //    // First create y_i  ( a total of N=# of nodes in the network variables
        //    System.Console.WriteLine("Creating y_i");

        //    for (int i = 0; i < N; i++)
        //    {
        //        //Integer-2
        //        vary_int = newColumn_init_integer(cplex_model, obj, 0, 0);
        //        vary_int.Name = "y" + node_set[i];
        //        vary_int_arr[i] = vary_int;
        //        expr_y_int[i] = vary_int;
        //        //lp_model.AddColumn(vary_int);
        //    }

        //    //Int-3
        //    lp_model.AddCols(vary_int_arr); // using the array version of adding columns

        //    System.Console.WriteLine("Creating x_ir");
        //    //Next create x_irt ... the variables representing activation of a node-i in monte carlo run-r at the cascade step-t

        //    int counter = 0;
        //    for (int r = 0; r < trial_limit; r++)
        //    {
        //        for (int i = 0; i < N; i++)
        //        {

        //            //int-4
        //            varx_int = newColumn_init_integer(cplex_model, obj, 1, 0);
        //            varx_int.Name = "x" + (node_set[i]) + "_" + (r + 1);
        //            varx_int_arr[counter] = varx_int;
        //            //lp_model.AddColumn(varx_int);
        //            expr_x[i, r] = varx_int;

        //            counter++;
        //        }
        //    }

        //    //Int-5
        //    lp_model.AddCols(varx_int_arr); // using the array version of adding columns

        //    //----------------------------------------------------------
        //    //--------------- create the constraints
        //    INumExpr temp_exp = null;
        //    IRange rngy;
        //    IRange[] rng_arr;


        //    System.Console.WriteLine("Starting the constraints... Total : " + (trial_limit * N + 1) + " constraints");
        //    // exactly k initial active users
        //    for (int i = 0; i < N; i++)
        //    {
        //        if (i == 0)
        //        {
        //            //int-6
        //            temp_exp = cplex_model.Prod(recruitment_cost[i], expr_y_int[i]);
        //            //temp_exp = expr_y_int[i];
        //        }
        //        else
        //        {
        //            //int-7
        //            temp_exp = cplex_model.Sum(temp_exp, cplex_model.Prod(recruitment_cost[i], expr_y_int[i]));
        //            //temp_exp = cplex_model.Sum(temp_exp, expr_y_int[i]);
        //        }
        //    }

        //    //rngy = cplex_model.AddEq(k_init, temp_exp);
        //    rngy = cplex_model.AddGe(BUDGET, temp_exp);
        //    lp_model.AddRow(rngy);

        //    //--- influence constraints x_i_r <= Sum_j (y_j)          j in all accessing nodes to i          (total of N.R constraints)
        //    string[] neigh_arr;

        //    temp_exp = cplex_model.NumExpr();
        //    INumExpr temp_exp2 = cplex_model.NumExpr();
        //    rng_arr = new IRange[trial_limit * N];
        //    int j = 0;
        //    counter = 0;

        //    for (int r = 0; r < trial_limit; r++)
        //    {
        //        for (int i = 0; i < N; i++)
        //        {

        //            //int-8
        //            temp_exp = expr_x[i, r];

        //            // now add the neighbours with x_j terms

        //            if (SAA_tree_list[r][i] != null)
        //            {
        //                foreach (int node in SAA_tree_list[r][i])   //my predecessors can activate me
        //                {
        //                    {
        //                        //int-10
        //                        temp_exp = cplex_model.Sum(temp_exp, cplex_model.Prod(-1, expr_y_int[node]));
        //                    }
        //                }
        //                rngy = cplex_model.AddGe(0, temp_exp);
        //                rng_arr[counter] = rngy;
        //                counter++;

        //            }       //end of if for null neighbourhood
        //        }           //end of for loop for nodes
        //    }               //end of for loop for sample size R

        //    // manual cover inequalities
        //    int add_cuts = 0;
        //    /*
        //    if(add_cuts==1)
        //    {
        //        temp_exp = cplex_model.Sum(expr_y[11], expr_y[19], expr_y[21]);
        //        rngy = cplex_model.AddGe(2, temp_exp);
        //        temp_exp = cplex_model.Sum(expr_y[11], expr_y[19], expr_y[20]);
        //        rngy = cplex_model.AddGe(2, temp_exp);
        //        temp_exp = cplex_model.Sum(expr_y[11], expr_y[19], expr_y[10]);
        //        rngy = cplex_model.AddGe(2, temp_exp);
        //        temp_exp = cplex_model.Sum(expr_y[11], expr_y[19], expr_y[8]);
        //        rngy = cplex_model.AddGe(2, temp_exp);
        //        temp_exp = cplex_model.Sum(expr_y[11], expr_y[19], expr_y[22]);
        //        rngy = cplex_model.AddGe(2, temp_exp);
        //        temp_exp = cplex_model.Sum(expr_y[11], expr_y[19], expr_y[16]);
        //        rngy = cplex_model.AddGe(2, temp_exp);
        //    }*/

        //    // fixing some variables
        //    if (SAA_type == 1)
        //    {
        //        for (int i = 0; i < N; i++)
        //        {
        //            //lp-11
        //            //temp_exp = expr_y[i];

        //            //int-11
        //            temp_exp = expr_y_int[i];
        //            if (SAA_current_list.Contains((int)i))
        //            {
        //                rngy = cplex_model.AddEq(1, temp_exp);
        //            }
        //            else
        //            {
        //                rngy = cplex_model.AddEq(0, temp_exp);
        //            }
        //        }

        //    }
        //    //IRange[] rng_arr_new = new IRange[counter];
        //    //for (int t = 0; t < counter; t++)
        //    //    rng_arr_new[t] = rng_arr[t];

        //    //lp_model.AddRows(rng_arr_new);

        //    //if (save_model == 1)
        //    {
        //        cplex_model.ExportModel("model" + SAA_m + ".mps");
        //    }
        //    double solution = -1;
        //    solution = cplex_solve(cplex_model, SAA_m) / trial_limit;
        //    lp_model.Clear();
        //    cplex_model.End();
        //    swvar.WriteLine("Sample-" + SAA_m);
        //    return solution;
        //}

        //public static double model_import(int k)
        //{
        //    cplex_model = new Cplex();
        //    cplex_model.ImportModel("model.lp");


        //    double solution = -1;
        //    //solution = cplex_solve(cplex_model) / trial_limit;
        //    //lp_model.Clear();
        //    cplex_model.End();
        //    return solution;

        //}

        //public static double cplex_solve(Cplex cplexvar, int SAA_m)
        //{
        //    double solution = -1;
        //    try
        //    {
        //        //cplex.SetParam(Cplex.IntParam.RootAlg, Cplex.Algorithm.Network);
        //        try
        //        {
        //            cplexvar.SetParam(Cplex.IntParam.AdvInd, 1);
        //            cplexvar.SetParam(Cplex.IntParam.TimeLimit, Cplex_seconds);
        //            cplexvar.SetParam(Cplex.DoubleParam.EpGap, param_epgap);
        //            // Solve the model and display the solution if one was found
        //            if (cplexvar.Solve())
        //            {
        //                //cplex_model.ExportModel("modelfinal.lp");
        //                // System.Console.WriteLine("Solution status = " + cplexvar.GetStatus());
        //                System.Console.WriteLine("Solution value  = " + cplexvar.ObjValue);
        //                solution = cplexvar.ObjValue;
        //                double relativegap = cplexvar.MIPRelativeGap;
        //                double upperbound = cplexvar.GetBestObjValue();
        //                if (relativegap > 0.05)
        //                    solution = Math.Floor(upperbound);
        //                INumVar[] vars = lp_model.NumVars;

        //                vars = lp_model.NumVars;
        //                IRange[] cstrts = lp_model.Ranges;

        //                double[] x = cplexvar.GetValues(lp_model);
        //                List<int> SAA_sample_result = new List<int>(k_init);

        //                for (int j = 0; j < N; ++j)
        //                {

        //                    if (x[j] >= 0.000001)
        //                    {
        //                        swvar.WriteLine(vars[j].Name + " = " + x[j]);
        //                        result_set.Add(node_set[j]);
        //                        SAA_sample_result.Add((int)j);
        //                    }
        //                }
        //                SAA_list.Add(SAA_sample_result);

        //                if (save_log2 == 1)
        //                {
        //                    //StreamWriter swvar2 = new StreamWriter("log2.txt");
        //                    swvar2.WriteLine("Solution value  = " + cplexvar.ObjValue);
        //                    for (int j = 0; j < x.Length; ++j)
        //                    {

        //                        if (x[j] >= 0.000001)
        //                        {
        //                            swvar2.WriteLine(vars[j].Name + " = " + x[j]);
        //                        }
        //                    }
        //                    //swvar2.Close();
        //                }
        //                /*
        //                for (int j = 0; j < x.Length; ++j)
        //                {
        //                    swvar.WriteLine(vars[j].Name + " = " + x[j]);
        //                }
        //                */

        //            }
        //        }
        //        catch (ILOG.Concert.Exception e)
        //        {
        //            System.Console.WriteLine(e);
        //            //   swvar.WriteLine("Concert exception caught: " + e);
        //            solution = -2;
        //        }
        //    }
        //    catch (ILOG.Concert.Exception e)
        //    {
        //        System.Console.WriteLine("Concert exception caught: " + e);
        //        solution = -1;
        //    }
        //    return solution;
        //}

        //public static INumVar newColumn_init(IMPModeler modeler, IObjective obj, double objval, double colval)
        //{
        //    Column objcol = modeler.Column(obj, objval);
        //    //Column rngcol = modeler.Column(rng, colval);
        //    return modeler.NumVar(objcol, 0.0, 1);
        //}

        //public static IIntVar newColumn_init_integer(IMPModeler modeler, IObjective obj, double objval, double colval)
        //{
        //    Column objcol = modeler.Column(obj, objval);
        //    //Column rngcol = modeler.Column(rng, colval);
        //    return modeler.BoolVar(objcol);
        //}

        //#endregion

        #region Gurobi

        public static double mip_TIPTOP()
        {
            //trial_limit = SAA_N2;
            Stopwatch swT = new Stopwatch();
            swT.Start();
            tiptop_rho = 1.0 / N; SAA_LR_list = new List<List<int>>(SAA_M);
            UInt64 trial_limit = Convert.ToUInt64((1 + tiptop_eps) * (2 + 0.6666 * tiptop_eps) * (1 / (tiptop_eps * tiptop_eps)) * Math.Log(2 / tiptop_rho)) * 10;
            System.Console.WriteLine("Constructing the TIPTOP Model with Gurobi...");
            System.Console.WriteLine("First do the sampling..." + trial_limit + " samples");
            Random rnd = new Random();
            y_obj = new double[N];
            x_exist = new bool[trial_limit, 1];
            hypernodes = new List<List<int>>();
            node_score = new long[N];
            List<int> BFS_result = new List<int>();
            int r_counter = 0;
            for (UInt64 r = 0; r < trial_limit; r++)
            {
                int selected_node = (int)rnd.Next(N);
                hypernodes.Add(new List<int>());
                hypernodes[r_counter].Add(selected_node);
                node_score[selected_node]++;
                BFS_result = BFS_TipTop(selected_node);
                if (BFS_result.Count > 0)
                {
                    hypernodes[r_counter].AddRange(BFS_result);
                    x_exist[r, 0] = true;
                    r_counter++;
                }
                else
                {// y_selected_node++
                    x_exist[r, 0] = false;
                    y_obj[selected_node]++;
                    hypernodes[r_counter].Clear();
                    hypernodes.RemoveAt(r_counter);
                }
            }

            swT.Stop(); TimeSpan swT_elapsed = swT.Elapsed; double T_t1 = System.Convert.ToDouble(swT_elapsed.Ticks); swT.Reset(); swT.Start();
            double solutionLR = -1; double solution = -1;
            solutionLR = LR_Tiptop(1, 0, r_counter); string SAA_str_solution = "";
            swT.Stop(); TimeSpan swT_elapsed2 = swT.Elapsed; double T_t2 = System.Convert.ToDouble(swT_elapsed2.Ticks); swT.Reset(); swT.Start();
            try
            {
                GRBEnv env = new GRBEnv("mip1.log");
                GRBModel model = new GRBModel(env);
                //model.Parameters.Presolve = 1;
                model.Parameters.TimeLimit = 3600;

                GRBVar[] y_j = new GRBVar[N];
                GRBVar[] x_r = new GRBVar[trial_limit];

                System.Console.WriteLine("Creating y_i");
                for (int i = 0; i < N; i++)
                {
                    y_j[i] = model.AddVar(0.0, 1.0, y_obj[i], GRB.BINARY, "y_" + i);
                }

                model.ModelSense = GRB.MAXIMIZE;

                //----------------------------------------------------------
                //--------------- create the constraints
                int counter = 0;
                GRBLinExpr temp_exp2;
                temp_exp2 = 0.0;
                System.Console.WriteLine("Starting the constraints... Total : " + ((long)trial_limit * N + 1) + " constraints");
                // exactly k initial active users
                for (int i = 0; i < N; i++)
                {
                    temp_exp2.AddTerm(1.0, y_j[i]);
                }

                model.AddConstr(temp_exp2 == k_init, "constraint_y");

                //--- influence constraints x_r <= Sum_j (y_j)          j in all accessing nodes to i          (total of N.R constraints)
                //string[] neigh_arr;


                GRBLinExpr temp_exp;

                int j = 0;

                temp_exp = 0.0;
                int counter2 = 0;

                for (int r = 0; r < r_counter; r++)
                {
                    //if (x_exist[r,0] == true)
                    {
                        x_r[r] = model.AddVar(0.0, 1.0, 1.0, GRB.CONTINUOUS, "x_" + r);
                        temp_exp.AddTerm(1.0, x_r[r]);

                        //if (SAA_tree_list[r][i].Count <= N)
                        {
                            foreach (int node in hypernodes[r])   //my predecessors can activate me
                            {
                                {
                                    temp_exp.AddTerm(-1, y_j[(int)node]);
                                }
                            }
                            model.AddConstr(temp_exp <= 0, "constraint" + (counter + 1));
                            counter++;
                        }



                    }       //end of if for null neighbourhood
                    temp_exp = 0.0;
                }               //end of for loop for sample size R


                //model.Write("modelGRB2" + SAA_m + ".mps");
                //model.Write("model_tip.lp");
                //GRBModel p = model.Presolve();
                //p.Write("presolve.lp");
                model.Optimize();

                if (model.Status == GRB.Status.OPTIMAL)
                {
                    Console.WriteLine("Obj: " + model.Get(GRB.DoubleAttr.ObjVal));
                    solution = model.Get(GRB.DoubleAttr.ObjVal);


                    List<int> SAA_sample_result = new List<int>(k_init);
                    int isfractional = 0;
                    for (int jj = 0; jj < N; ++jj)
                    {

                        if (y_j[jj].X > 0.001)
                        {
                            //result_set.Add(node_set[jj]);
                            result_set.Add(node_set[jj]);
                            SAA_sample_result.Add((int)jj);
                            System.Console.WriteLine(y_j[jj].VarName + "(" + node_set[jj] + ")=" + y_j[jj].X);
                            SAA_str_solution = SAA_str_solution + ";" + node_set[jj].ToString();
                            if (y_j[jj].X < 0.9)
                            {
                                System.Console.WriteLine("Fractional value found");
                                System.Console.ReadKey();
                                isfractional = 1;
                            }
                        }
                    }
                    if (isfractional == 1)
                    {
                        System.Console.WriteLine("To conitnue click...");
                        System.Console.ReadKey();
                    }

                }
                else
                {
                    Console.WriteLine("No solution");
                    solution = 0;
                }

                // Dispose of model and env

                model.Dispose();
                env.Dispose();


            }
            catch (GRBException e)
            {
                Console.WriteLine("Error code: " + e.ErrorCode + ". " + e.Message);
            }


            swT.Stop(); TimeSpan swT_elapsed3 = swT.Elapsed; double T_t3 = System.Convert.ToDouble(swT_elapsed3.Ticks); swT.Reset();
            string LR_best_seed = "";
            foreach (int item in SAA_LR_list[0])
            {
                LR_best_seed = LR_best_seed + ";" + node_set[item].ToString();
            }
            string sqltext;
            string constr = "Server=localhost\\SQLExpress;Database=research;User Id=doktora;Password=cesmede;";
            SqlConnection conn = new SqlConnection(constr);
            conn.Open();
            SqlCommand command = conn.CreateCommand();

            {
                sqltext = "INSERT INTO BIMP_SAA (SAA_M,SAA_N1,SAA_N2,SAA_N3,modelID, diffusion_modelID,K,network_sampleID,node_size,edge_size,duration,z_star,SAA_z, SAA_z2, SAA_z3,solution_y, propagation_prop, budget,R1_std, T2_std,z_pipageLP,z_pipageIP,z_pipageInf,t_pipage,pipage_solution,pipage_count, z_LRUB, z_LRLB, z_LRinf,t_LR, solution_LR, stdev_LRUB, stdev_LRinf, fixed_p, LR_iter) VALUES (" + SAA_M + "," + SAA_N1 + "," + SAA_N2 + "," + SAA_N3 + ",1,1," + k_init + ",1," + N + "," + E + ",0,-1," + SA_1_hat_obj + "," + solution + "," + SA_3_obj + ",'" + SAA_str_solution + "'," + prop_prob + ",'" + BUDGET + "','" + R1_std + "','" + T2_std + "'," + pipage_objective_LP + "," + pipage_objective_IP + "," + z_pipageInf + "," + (T_t1 + T_t3) + ",'" + pipage_solution + "','" + pipage_count + "'," + z_LRUB + "," + solutionLR + ",0" + "," + (T_t1 + T_t2) + ",'" + LR_best_seed + "',0,0," + fixed_probability + "," + no_of_LR_iter + ")";
                sqltext = sqltext.Replace("'NaN'", "'0'");
                command.CommandText = sqltext;
                command.ExecuteNonQuery();
            }


            return solution;
        }


        public static double construct_model2_gurobi(int SAA_m, int SAA_type, int sample_size)
        {
            trial_limit = sample_size;
            System.Console.WriteLine("Constructing the MIP with Gurobi...");
            double solution = -1;
            try
            {
                GRBEnv env = new GRBEnv("mip1.log");
                GRBModel model = new GRBModel(env);
                //GRBModel model = new GRBModel(env, "modelGRB20cc.lp");
                //model.Optimize();
                //model = new GRBModel(env, "model0.mps");
                //model.Optimize();
                //model.Parameters.Presolve = 1;

                GRBVar[] y_j = new GRBVar[N];
                GRBVar[,] x_ir = new GRBVar[N, sample_size];
                List<GRBVar> v_j = new List<GRBVar>();

                //GRBConstr[] myconstraints = new GRBConstr[2] { model.GetConstrByName("c1"), model.GetConstrByName("c2") };
                //double[] mycoeffs = new double[2] { 2, 2 };
                //GRBVar y = model.AddVar(0, 1, 0, GRB.CONTINUOUS, myconstraints, mycoeffs,"y");
                //model.Parameters.NodefileStart=0.5;

                System.Console.WriteLine("Creating y_i");
                for (int i = 0; i < N; i++)
                {
                    y_j[i] = model.AddVar(0.0, 1.0, y_obj[i], GRB.BINARY, "y_" + i);
                }

                System.Console.WriteLine("Creating x_ir");
                //for (int i = 0; i < N; i++)
                //  for (int r = 0; r < sample_size; r++)
                {
                    //x_ir[i, r] = model.AddVar(0.0, 1.0, 1.0, GRB.CONTINUOUS, "x_" + i + "_" + r);
                }

                model.ModelSense = GRB.MAXIMIZE;

                //----------------------------------------------------------
                //--------------- create the constraints
                int counter = 0;
                GRBLinExpr temp_exp2;
                temp_exp2 = 0.0;
                System.Console.WriteLine("Starting the constraints... Total : " + (trial_limit * N + 1) + " constraints");
                // exactly k initial active users
                for (int i = 0; i < N; i++)
                {
                    temp_exp2.AddTerm(1.0, y_j[i]);
                }

                model.AddConstr(temp_exp2 == k_init, "constraint_y");

                //--- influence constraints x_i_r <= Sum_j (y_j)          j in all accessing nodes to i          (total of N.R constraints)
                //string[] neigh_arr;


                GRBLinExpr temp_exp;

                int j = 0;

                temp_exp = 0.0;
                int counter2 = 0;

                for (int r = 0; r < trial_limit; r++)
                {
                    for (int i = 0; i < N; i++)
                    {
                        //if (SAA_tree_list[r][i].Count > 0)
                        if (x_exist[r, i] == true)
                        {
                            x_ir[i, r] = model.AddVar(0.0, 1.0, 1.0, GRB.CONTINUOUS, "x_" + i + "_" + r);
                            temp_exp.AddTerm(1.0, x_ir[i, r]);

                            //if (SAA_tree_list[r][i].Count <= N)
                            {
                                foreach (int node in SAA_tree_list[r][i])   //my predecessors can activate me
                                {
                                    {
                                        temp_exp.AddTerm(-1, y_j[(int)node]);
                                    }
                                }
                                model.AddConstr(temp_exp <= 0, "constraint" + (counter + 1));
                                counter++;
                            }



                        }       //end of if for null neighbourhood
                        temp_exp = 0.0;
                    }           //end of for loop for nodes
                }               //end of for loop for sample size R


                //model.Write("modelGRB2" + SAA_m + ".mps");
                //model.Write("modelGRB2" + SAA_m + ".lp");
                //GRBModel p = model.Presolve();
                //p.Write("presolve.lp");
                model.Optimize();

                if (model.Status == GRB.Status.OPTIMAL)
                {
                    Console.WriteLine("Obj: " + model.Get(GRB.DoubleAttr.ObjVal));
                    solution = model.Get(GRB.DoubleAttr.ObjVal);


                    List<int> SAA_sample_result = new List<int>(k_init);
                    int isfractional = 0;
                    for (int jj = 0; jj < N; ++jj)
                    {

                        if (y_j[jj].X > 0.001)
                        {
                            //result_set.Add(node_set[jj]);
                            result_set.Add(node_set[jj]);
                            SAA_sample_result.Add((int)jj);
                            System.Console.WriteLine(y_j[jj].VarName + "=" + y_j[jj].X);
                            if (y_j[jj].X < 0.9)
                            {
                                System.Console.WriteLine("Fractional value found");
                                System.Console.ReadKey();
                                isfractional = 1;
                            }
                        }
                    }
                    if (isfractional == 1)
                    {
                        System.Console.WriteLine("To conitnue click...");
                        System.Console.ReadKey();
                    }

                    SAA_list.Add(SAA_sample_result);


                }
                else
                {
                    Console.WriteLine("No solution");
                    solution = 0;
                }

                // Dispose of model and env

                model.Dispose();
                env.Dispose();


            }
            catch (GRBException e)
            {
                Console.WriteLine("Error code: " + e.ErrorCode + ". " + e.Message);
            }


            return solution;
        }

        public static double construct_model2_gurobi_kucukyavuz(int SAA_m, int SAA_type, int sample_size) // x_ir model with LP + pipage
        {
            trial_limit = sample_size;
            System.Console.WriteLine("Constructing the LazyCutModel with Gurobi...");
            double solution = -1;
            try
            {
                GRBEnv env = new GRBEnv("mip1.log");
                GRBModel model = new GRBModel(env);
                model.Parameters.Method = 1;

                //GRBVar x=new GRBVar;
                GRBVar[] y_j = new GRBVar[N];
                GRBVar[,] x_ir = new GRBVar[N, sample_size];

                System.Console.WriteLine("Creating y_i");
                for (int i = 0; i < N; i++)
                {
                    y_j[i] = model.AddVar(0.0, 1.0, 0.0, GRB.BINARY, "y_" + i);
                }

                System.Console.WriteLine("Creating x_ir");
                for (int i = 0; i < N; i++)
                    for (int r = 0; r < sample_size; r++)
                    {
                        x_ir[i, r] = model.AddVar(0.0, 1.0, 1.0, GRB.CONTINUOUS, "x_" + i + "_" + r);
                    }

                model.ModelSense = GRB.MAXIMIZE;

                //----------------------------------------------------------
                //--------------- create the constraints
                int counter = 0;
                GRBLinExpr temp_exp2;
                temp_exp2 = 0.0;
                System.Console.WriteLine("Starting the constraints... Total : " + (trial_limit * N + 1) + " constraints");
                // exactly k initial active users
                for (int i = 0; i < N; i++)
                {
                    temp_exp2.AddTerm(1.0, y_j[i]);
                }

                model.AddConstr(temp_exp2 == k_init, "constraint-y");


                GRBLinExpr temp_exp;

                temp_exp = 0.0;

                for (int r = 0; r < sample_size; r++)
                {
                    for (int i = 0; i < N; i++)
                    {
                        temp_exp.AddTerm(1.0, x_ir[i, r]);
                    }
                    model.AddConstr(temp_exp <= N, "constraint-1_" + (r + 1));
                    temp_exp = 0.0;

                }

                model.Optimize();
                model.Write("model_KY_0" + SAA_m + ".lp");
                if (model.Status == GRB.Status.OPTIMAL)
                {
                    Console.WriteLine("Obj: " + model.Get(GRB.DoubleAttr.ObjVal));
                    solution = model.Get(GRB.DoubleAttr.ObjVal);
                    //LP_duals = model.Get(GRB.DoubleAttr.Pi, model.GetConstrs());
                    //model.Get(GRB.DoubleAttr.)
                    List<int> SAA_sample_result = new List<int>(k_init);

                    List<int> y_list = new List<int>();
                    double[] yj_vals = new double[N];
                    double[,] x_ir_vals = new double[N, sample_size];
                    for (int jj = 0; jj < N; ++jj)
                    {
                        yj_vals[jj] = y_j[jj].X;
                        if (yj_vals[jj] > 0.001)
                        {
                            result_set.Add(node_set[jj]);
                            y_list.Add((int)jj);
                            //SAA_sample_result.Add(jj);
                            System.Console.WriteLine(y_j[jj].VarName + "=" + y_j[jj].X);
                            System.Console.WriteLine(node_set[jj]);
                            swvar.WriteLine(y_j[jj].VarName + "=" + y_j[jj].X);
                        }
                    }

                    for (int jj = 0; jj < N; ++jj)
                    {
                        for (int r = 0; r < sample_size; r++)
                        {
                            x_ir_vals[jj, r] = x_ir[jj, r].X;
                        }
                    }

                    double UB = solution;
                    double LB = -1;
                    double LB_best = -1;
                    int looper = 0;
                    List<int> ybest = new List<int>();

                    do
                    {
                        looper++;
                        List<List<List<int>>> SAA_temp_tree_list = new List<List<List<int>>>();
                        double[] theta = new double[sample_size];
                        double[] sigma = new double[sample_size];
                        double theta_ctr = 0; LB = 0;

                        for (int r = 0; r < sample_size; r++)
                        {
                            System.Console.Write("-" + r); theta_ctr = 0;
                            SAA_temp_tree_list.Add(new List<List<int>>());
                            for (int i = 0; i < N; i++)
                            {
                                double theta_local = 0;
                                SAA_temp_tree_list[r].Add(new List<int>());
                                int delete_ir = 0;
                                List<int> tl = new List<int>();
                                tl.AddRange(SAA_tree_list[r][i]);
                                for (int j2 = 0; j2 < y_list.Count; j2++)
                                {
                                    if (tl.IndexOf((int)y_list[j2]) >= 0)
                                    {
                                        delete_ir = 1;
                                        theta_local = theta_local + yj_vals[y_list[j2]];
                                        //break;
                                    }
                                }
                                if (delete_ir == 0)
                                    SAA_temp_tree_list[r][i].AddRange(SAA_tree_list[r][i]);
                                if (theta_local > 1)
                                    theta_local = 1;
                                if (theta_local < 1 && theta_local > 0)
                                    theta_local = theta_local * 1;
                                theta_ctr = theta_ctr + theta_local;
                            }
                            theta[r] = theta_ctr;
                            LB = LB + theta[r];
                        }
                        if (LB_best < LB)
                        {
                            LB_best = LB;
                            Console.WriteLine("LB_best: " + LB_best);
                            ybest.Clear();
                            ybest.AddRange(y_list);
                        }
                        Console.WriteLine("LB: " + LB);
                        Console.WriteLine("LB_best: " + LB_best);
                        int[,] coeff = new int[sample_size, N];


                        for (int r = 0; r < sample_size; r++)
                        {
                            temp_exp = 0.0;
                            System.Console.Write("-" + r);
                            for (int j2 = 0; j2 < N; j2++)
                            {
                                coeff[r, j2] = 0;
                                temp_exp.AddTerm(1.0, x_ir[j2, r]);
                                if (y_list.IndexOf((int)j2) < 0)
                                {
                                    for (int i = 0; i < N; i++)
                                    {
                                        List<int> tl = new List<int>();
                                        tl.AddRange(SAA_temp_tree_list[r][i]);
                                        if (tl.IndexOf((int)j2) >= 0)
                                        {
                                            coeff[r, j2]++;
                                        }
                                    }
                                }
                                temp_exp.AddTerm(-1 * coeff[r, j2], y_j[j2]);
                                sigma[r] = sigma[r] + x_ir_vals[j2, r];
                            }
                            if (sigma[r] > theta[r])
                                model.AddConstr(temp_exp <= theta[r], "constraint-2" + looper + (r + 1));
                        }

                        model.Update();
                        model.Reset();
                        model.Optimize();
                        model.Write("model_KY" + looper + "_" + SAA_m + ".lp");
                        if (model.Status == GRB.Status.OPTIMAL)
                        {
                            Console.WriteLine("UB: " + model.Get(GRB.DoubleAttr.ObjVal));
                            y_list.Clear();
                            for (int jj = 0; jj < N; ++jj)
                            {
                                yj_vals[jj] = y_j[jj].X;
                                if (yj_vals[jj] > 0.0001)
                                {
                                    y_list.Add((int)jj);
                                    //SAA_sample_result.Add(jj);
                                    System.Console.WriteLine(y_j[jj].VarName + "=" + y_j[jj].X);
                                }
                            }
                            for (int jj = 0; jj < N; ++jj)
                            {
                                for (int r = 0; r < sample_size; r++)
                                {
                                    x_ir_vals[jj, r] = x_ir[jj, r].X;
                                }
                            }
                            UB = model.Get(GRB.DoubleAttr.ObjVal);
                        }
                    } while (UB - LB_best > 0.1 && looper < 30);

                    for (int j = 0; j < ybest.Count; j++)
                        System.Console.WriteLine(" y_" + node_set[(int)ybest[j]] + "( " + ybest[j] + ")");
                    System.Console.WriteLine("z= " + LB_best);

                    pipage_solution = "";
                    for (int i = 0; i < N; i++)
                    {
                        //if (y_LP[i] >= 0.999)
                        {
                            pipage_solution = pipage_solution + "," + node_set[i];
                            SAA_sample_result.Add((int)i);
                        }
                    }
                    SAA_pipage_list.Add(SAA_sample_result);
                    //pipage_count = pipage_count + "," + counter_pipage.ToString();


                }
                else
                {
                    Console.WriteLine("No solution");
                    solution = 0;
                }

                // Dispose of model and env

                model.Dispose();
                env.Dispose();

            }
            catch (GRBException e)
            {
                Console.WriteLine("Error code: " + e.ErrorCode + ". " + e.Message);
            }


            return solution;
        }

        public static double calculate_pipage_F(GRBVar[] y, int SAA_m)
        {
            double val = 0;
            double sum = 0;
            int j = -1;

            for (int r = 0; r < trial_limit; r++)
            {
                for (int i = 0; i < N; i++)
                {
                    val = 1;
                    if (SAA_tree_list[r][i] != null && x_exist[r, i] == true)
                    {
                        foreach (int node in SAA_tree_list[r][i])   //my predecessors can activate me
                        {
                            {
                                val = val * (1 - y[node].X);
                            }
                        }
                    }       //end of if for null neighbourhood
                    sum = sum + (1 - val);
                    if (r == 0)
                        sum = sum + y_obj[i] * y[i].X;
                }           //end of for loop for nodes
            }
            return sum;
        }

        public static double calculate_pipage_F_mu(double[] y, int SAA_m, int j1, int j2, double eps)
        {
            double val = 0;
            double sum = 0;
            int j = -1;
            y[j1] = y[j1] + eps;
            y[j2] = y[j2] - eps;

            for (int r = 0; r < trial_limit; r++)
            {
                for (int i = 0; i < N; i++)
                {
                    val = 1;
                    if (SAA_tree_list[r][i].Count > 0 && x_exist[r, i] == true)
                    {
                        foreach (int node in SAA_tree_list[r][i])   //my predecessors can activate me
                        {
                            {
                                val = val * (1 - y[node]);
                            }
                        }
                    }       //end of if for null neighbourhood
                    sum = sum + (1 - val);
                    if (r == 0)
                        sum = sum + y_obj[i] * y[i];
                }           //end of for loop for nodes
            }
            y[j1] = y[j1] - eps;
            y[j2] = y[j2] + eps;
            return sum;
        }

        public static int count_fractionals(GRBVar[] y, int SAA_m)
        {
            int counter = 0;
            for (int jj = 0; jj < N; ++jj)
            {

                if (y[jj].X > 0.001)
                {
                    if (y[jj].X < 0.999)
                    {
                        counter++;
                    }
                }
            }
            return counter;
        }

        public static int count_fractionals_yLP(double[] y, int SAA_m)
        {
            int counter = 0;
            for (int jj = 0; jj < N; ++jj)
            {

                if (y[jj] > 0.001)
                {
                    if (y[jj] < 0.999)
                    {
                        counter++;
                    }
                }
            }
            return counter;
        }

        public static double[] get_yLP_from_y(GRBVar[] y, int SAA_m)
        {
            double[] y_LP = new double[N];
            for (int i = 0; i < N; i++)
            {
                y_LP[i] = y[i].X;
            }
            return y_LP;
        }

        public static double construct_model2_gurobi_LP(int SAA_m, int SAA_type, int sample_size, int the_cut) // x_ir model with LP + pipage
        {
            trial_limit = sample_size;
            System.Console.WriteLine("Constructing the MIP with Gurobi...");
            double solution = -1;

            //List<int> dominated = new List<int>();
            //if (SAA_type == 1)
            //    dominated = reduce_tree_list();

            try
            {
                GRBEnv env = new GRBEnv("mip1.log");
                GRBModel model = new GRBModel(env);
                //model.Parameters.Method = 1;
                //model.Parameters.DegenMoves = 0;

                //GRBVar x=new GRBVar;
                GRBVar[] y_j = new GRBVar[N];
                GRBVar[,] x_ir = new GRBVar[N, sample_size];
                List<GRBVar> v_j = new List<GRBVar>();

                System.Console.WriteLine("Creating y_i");
                for (int i = 0; i < N; i++)
                {
                    y_j[i] = model.AddVar(0.0, 1.0, y_obj[i], GRB.CONTINUOUS, "y_" + i);
                }

                System.Console.WriteLine("Creating x_ir");
                //for (int i = 0; i < N; i++)
                //  for (int r = 0; r < sample_size; r++)
                {
                    //x_ir[i, r] = model.AddVar(0.0, 1.0, 1.0, GRB.CONTINUOUS, "x_" + i + "_" + r);
                }

                model.ModelSense = GRB.MAXIMIZE;

                //----------------------------------------------------------
                //--------------- create the constraints
                int counter = 0;
                GRBLinExpr temp_exp2;
                temp_exp2 = 0.0;
                System.Console.WriteLine("Starting the constraints... Total : " + (trial_limit * N + 1) + " constraints");
                // exactly k initial active users
                for (int i = 0; i < N; i++)
                {
                    temp_exp2.AddTerm(1.0, y_j[i]);
                }

                model.AddConstr(temp_exp2 == k_init, "constraint_y");

                //--- influence constraints x_i_r <= Sum_j (y_j)          j in all accessing nodes to i          (total of N.R constraints)
                //string[] neigh_arr;


                GRBLinExpr temp_exp;

                int j = 0;

                temp_exp = 0.0;
                int counter2 = 0;
                int limit = N;
                if (SAA_type == 1)
                    limit = 2;

                for (int r = 0; r < trial_limit; r++)
                {
                    for (int i = 0; i < N; i++)
                    {
                        //if (SAA_tree_list[r][i].Count > 0)
                        if (x_exist[r, i] == true)
                        {
                            x_ir[i, r] = model.AddVar(0.0, 1.0, 1.0, GRB.CONTINUOUS, "x_" + i + "_" + r);
                            temp_exp.AddTerm(1.0, x_ir[i, r]);

                            //if (SAA_tree_list[r][i].Count <= limit)
                            {
                                foreach (int node in SAA_tree_list[r][i])   //my predecessors can activate me
                                {
                                    {
                                        temp_exp.AddTerm(-1, y_j[(int)node]);
                                    }
                                }
                                model.AddConstr(temp_exp <= 0, "constraint" + (counter + 1));
                                counter++;
                            }
                            //else
                            {
                                //List<int> templist = new List<int>();
                                //templist.AddRange(SAA_tree_list[r][i]);
                                //int item = -1;
                                //do
                                //{
                                //    item = (int)templist[0];
                                //    temp_exp.AddTerm(-1, y_j[item]);
                                //    v_j.Add(model.AddVar(0.0, 1.0, 0, GRB.CONTINUOUS, "v_" + counter2));
                                //    temp_exp.AddTerm(-1, v_j[counter2]);
                                //    templist.RemoveAt(0);
                                //    model.AddConstr(temp_exp <= 0, "constraintb" + (counter2 + 1));
                                //    counter++;
                                //    temp_exp = 0.0;
                                //    temp_exp.AddTerm(1.0, v_j[counter2]);
                                //    counter2++;
                                //} while (templist.Count > 2);
                                //item = (int)templist[0];
                                //temp_exp.AddTerm(-1, y_j[item]);
                                //item = (int)templist[1];
                                //temp_exp.AddTerm(-1, y_j[item]);
                                //model.AddConstr(temp_exp <= 0, "constraint" + (counter + 1));
                            }
                        }       //end of if for null neighbourhood
                        temp_exp = 0.0;
                    }           //end of for loop for nodes
                }


                string[] neigh_arr;
                //try cut sum_i x_ir <= a_j y_j
                if (the_cut == 1)
                {
                    //  determine_fwd_network_trees(trial_limit);
                    temp_exp = 0.0;
                    for (int r = 0; r < trial_limit; r++)
                    {
                        for (int i = 0; i < N; i++)
                        {
                            temp_exp.AddTerm(1.0, x_ir[i, r]);

                            if (SAA_fwd_tree[i, r, SAA_m] != null)
                            {
                                int pred_set_length = 0;
                                neigh_arr = SAA_fwd_tree[i, r, SAA_m].Split(new char[] { ',' });
                                pred_set_length = neigh_arr.Length;
                                temp_exp.AddTerm(-1 * pred_set_length, y_j[i]);
                            }
                            //else
                            //{
                            //    temp_exp.AddTerm(-1 , y_j[i]);
                            //    model.AddConstr(temp_exp <= 0, "cut_A_" + (counter + 1));
                            //}

                            //end of if for null neighbourhood
                        }           //end of for loop for nodes
                        model.AddConstr(temp_exp <= 0, "cut_A_" + (counter + 1));
                        counter++;
                        temp_exp = 0.0;
                    }
                }


                // Set objective: maximize x + y + 2 z

                //model.Write("model_LP" + SAA_m + ".lp");
                model.Optimize();

                if (model.Status == GRB.Status.OPTIMAL)
                {
                    Console.WriteLine("Obj: " + model.Get(GRB.DoubleAttr.ObjVal));
                    solution = model.Get(GRB.DoubleAttr.ObjVal);
                    LP_duals = model.Get(GRB.DoubleAttr.Pi, model.GetConstrs());
                    //model.Get(GRB.DoubleAttr.)
                    List<int> SAA_sample_result = new List<int>(k_init);

                    for (int jj = 0; jj < N; ++jj)
                    {

                        if (y_j[jj].X > 0.001)
                        {
                            result_set.Add(node_set[jj]);
                            //SAA_sample_result.Add(jj);
                            System.Console.WriteLine(y_j[jj].VarName + "=" + y_j[jj].X);
                            swvar.WriteLine(y_j[jj].VarName + "=" + y_j[jj].X);
                            if (y_j[jj].X < 0.9)
                            {
                                System.Console.WriteLine("Fractional value found");
                                //System.Console.ReadKey();
                            }
                        }
                    }

                    //for (int i = 0; i < N; i++)
                    //    for (int r = 0; r < sample_size; r++)
                    //    {
                    //        if (x_ir[i, r].X > 0.001)
                    //        {
                    //            //System.Console.WriteLine(x_ir[i, r].VarName + "=" + x_ir[i, r].X);
                    //            swvar.WriteLine(x_ir[i, r].VarName + "=" + x_ir[i, r].X);
                    //        }
                    //    }

                    //SAA_list.Add(SAA_sample_result);

                    //GRBConstr[] cnstrs = new GRBConstr[LP_duals.Length];
                    //cnstrs = model.GetConstrs();

                    //for (int i = 0; i < LP_duals.Length; i++)
                    //{
                    //    swvar.WriteLine(cnstrs[i].ConstrName + "_" + i + " : " + LP_duals[i]);
                    //}


                    // pipage
                    double F = 0;
                    int no_of_fractionals = count_fractionals(y_j, SAA_m);
                    pipage_objective_IP = calculate_pipage_F(y_j, SAA_m) / SAA_N1;
                    double[] y_LP = new double[N];
                    y_LP = get_yLP_from_y(y_j, SAA_m);
                    int counter_pipage = 0;
                    if (no_of_fractionals > 0)
                    {
                        int j1 = -1;
                        int j2 = -2;
                        double eps1 = 0;
                        double eps2 = 0;
                        double eps = 0;
                        double F1 = 0;
                        double F2 = 0;
                        do
                        {
                            int cntr = 0; counter_pipage++;
                            for (int i = 0; i < N; i++)
                            {
                                if (y_LP[i] < 0.999 && y_LP[i] > 0.001)
                                {
                                    if (cntr == 0)
                                    {
                                        j1 = i;
                                    }
                                    if (cntr == 1)
                                    {
                                        j2 = i;
                                    }
                                    cntr++;
                                    if (cntr >= 2)
                                        break;
                                }
                            }
                            //eps-1
                            if ((1 - y_LP[j1]) < y_LP[j2])
                                eps1 = 1 - y_LP[j1];
                            else
                                eps1 = y_LP[j2];
                            //eps-2
                            if (y_LP[j1] < (1 - y_LP[j2]))
                                eps2 = -1 * y_LP[j1];
                            else
                                eps2 = -1 * (1 - y_LP[j2]);
                            F1 = calculate_pipage_F_mu(y_LP, SAA_m, j1, j2, eps1);
                            F2 = calculate_pipage_F_mu(y_LP, SAA_m, j1, j2, eps2);
                            if (F1 >= F2)
                                eps = eps1;
                            else
                                eps = eps2;
                            y_LP[j1] = y_LP[j1] + eps;
                            y_LP[j2] = y_LP[j2] - eps;
                            if (cntr == 1)
                            {
                                if (y_LP[j1] > 0.5)
                                    y_LP[j1] = 1;
                                else
                                    y_LP[j1] = 0;
                            }
                            pipage_objective_IP = calculate_pipage_F_mu(y_LP, SAA_m, j1, j2, 0);
                        }
                        while (count_fractionals_yLP(y_LP, SAA_m) > 0);
                        pipage_objective_IP = pipage_objective_IP / SAA_N1;

                        System.Console.WriteLine("Pipage integer sol: " + pipage_objective_IP);
                    }
                    pipage_solution = "";
                    //selected_set2 = new List<int>();
                    for (int i = 0; i < N; i++)
                    {
                        if (y_LP[i] >= 0.999)
                        {
                            pipage_solution = pipage_solution + "," + node_set[i];
                            SAA_sample_result.Add((int)i);
                            //selected_set2.Add(node_set[i]);
                        }
                    }
                    SAA_pipage_list.Add(SAA_sample_result);
                    pipage_count = pipage_count + "," + counter_pipage.ToString();


                }
                else
                {
                    Console.WriteLine("No solution");
                    solution = 0;
                }

                // Dispose of model and env

                model.Dispose();
                env.Dispose();

            }
            catch (GRBException e)
            {
                Console.WriteLine("Error code: " + e.ErrorCode + ". " + e.Message);
            }


            return solution;
        }


        public static double gurobi_bipartite(int SAA_m, int SAA_type, int sample_size)
        {
            trial_limit = sample_size;
            System.Console.WriteLine("Constructing the Bipartite MIP with Gurobi...");
            double solution = -1;
            string[] neigh_arr;
            int counter = 0;

            try
            {
                GRBEnv env = new GRBEnv("mip1.log");
                GRBModel model = new GRBModel(env);

                //GRBVar x=new GRBVar;
                GRBVar[] y_j = new GRBVar[N];
                List<GRBVar> e_i = new List<GRBVar>();

                System.Console.WriteLine("Creating y_i");
                for (int i = 0; i < N; i++)
                {
                    y_j[i] = model.AddVar(0.0, 1.0, 0.0, GRB.BINARY, "y_" + i);
                }

                for (int i = 0; i < N; i++)
                {
                    for (int r = 0; r < sample_size; r++)
                    {
                        if (SAA_tree[i, r, SAA_m] != null)
                        {
                            neigh_arr = SAA_tree[i, r, SAA_m].Split(new char[] { ',' });
                            foreach (string str in neigh_arr)   //my predecessors can activate me
                            {
                                e_i.Add(model.AddVar(0.0, 1.0, 1.0, GRB.BINARY, "e_" + str + "_" + i + "_" + r));
                                counter++;
                            }
                        }
                    }
                }

                model.ModelSense = GRB.MAXIMIZE;

                //----------------------------------------------------------
                //--------------- create the constraints

                GRBLinExpr temp_exp2;
                temp_exp2 = 0.0;
                System.Console.WriteLine("Starting the constraints... Total : " + (trial_limit * N + 1) + " constraints");
                // exactly k initial active users
                for (int i = 0; i < N; i++)
                {
                    temp_exp2.AddTerm(1.0, y_j[i]);
                }

                model.AddConstr(temp_exp2 == k_init, "constraint" + (counter + 1));

                //--- influence constraints x_i_r <= Sum_j (y_j)          j in all accessing nodes to i          (total of N.R constraints)



                GRBLinExpr temp_exp;

                int j = 0;

                temp_exp = 0.0;
                counter = 0;
                int node_index = -1;
                for (int i = 0; i < N; i++)
                {
                    for (int r = 0; r < trial_limit; r++)
                    {
                        // now add the neighbours with x_j terms
                        if (SAA_tree[i, r, SAA_m] != null)
                        {
                            neigh_arr = SAA_tree[i, r, SAA_m].Split(new char[] { ',' });
                            foreach (string str in neigh_arr)   //my predecessors can activate me
                            {
                                node_index = Convert.ToUInt16(str);
                                temp_exp.AddTerm(-1.0, y_j[node_index]);
                                temp_exp.AddTerm(1.0, e_i[counter]);
                                model.AddConstr(temp_exp <= 0, "c3_" + str + "_" + i + "_" + r);
                                temp_exp = 0.0;
                                counter++;
                            }
                        }     //end of if for null neighbourhood
                    }           //end of for loop for nodes
                }               //end of for loop for sample size R

                // Set objective: maximize x + y + 2 z


                model.Optimize();
                //model.Write("model.lp");
                if (model.Status == GRB.Status.OPTIMAL)
                {
                    Console.WriteLine("Obj: " + model.Get(GRB.DoubleAttr.ObjVal));
                    solution = model.Get(GRB.DoubleAttr.ObjVal);

                    List<int> SAA_sample_result = new List<int>(k_init);

                    for (int jj = 0; jj < N; ++jj)
                    {

                        if (y_j[jj].X > 0.001)
                        {
                            result_set.Add(node_set[jj]);
                            SAA_sample_result.Add((int)jj);
                            if (y_j[jj].X < 0.9)
                            {
                                System.Console.WriteLine("Fractional value found");
                                System.Console.ReadKey();
                            }
                        }
                    }
                    SAA_list.Add(SAA_sample_result);


                }
                else
                {
                    Console.WriteLine("No solution");
                    solution = 0;
                }

                // Dispose of model and env

                model.Dispose();
                env.Dispose();

            }
            catch (GRBException e)
            {
                Console.WriteLine("Error code: " + e.ErrorCode + ". " + e.Message);
            }


            return solution;
        }


        public static double construct_model_pipage_manuel_LP(int SAA_m, int SAA_type, int sample_size)
        {
            trial_limit = sample_size;
            System.Console.WriteLine("Constructing the MIP with Gurobi...");
            double solution = -1;
            try
            {
                GRBEnv env = new GRBEnv("mip1.log");
                GRBModel model = new GRBModel(env);
                N = 18;
                sample_size = 136;
                k_init = 6;
                int p = 3;
                //GRBVar x=new GRBVar;
                GRBVar[] y_j = new GRBVar[N];
                GRBVar[,] x_ir = new GRBVar[N, sample_size];

                System.Console.WriteLine("Creating y_i");
                for (int i = 0; i < N; i++)
                {
                    y_j[i] = model.AddVar(0.0, 1.0, 0.0, GRB.CONTINUOUS, "y_" + i);
                }

                System.Console.WriteLine("Creating x_ir");
                for (int i = 0; i < N; i++)
                    for (int r = 0; r < sample_size; r++)
                    {
                        x_ir[i, r] = model.AddVar(0.0, 1.0, 1.0, GRB.CONTINUOUS, "x_" + i + "_" + r);
                    }

                model.ModelSense = GRB.MAXIMIZE;

                //----------------------------------------------------------
                //--------------- create the constraints
                int counter = 0;
                GRBLinExpr temp_exp2;
                temp_exp2 = 0.0;
                System.Console.WriteLine("Starting the constraints... Total : " + (trial_limit * N + 1) + " constraints");
                // exactly k initial active users
                for (int i = 0; i < N; i++)
                {
                    temp_exp2.AddTerm(1.0, y_j[i]);
                }

                model.AddConstr(temp_exp2 == k_init, "constraint-y");

                //--- influence constraints x_i_r <= Sum_j (y_j)          j in all accessing nodes to i          (total of N.R constraints)

                GRBLinExpr temp_exp;

                int j = 0;

                temp_exp = 0.0;

                for (int i = 0; i < N; i++)
                {
                    int i0 = i;

                    for (int i1 = 0; i1 < N; i1++)
                    {
                        if (i1 != i0)
                        {
                            for (int i2 = 0; i2 < N; i2++)
                            {
                                if (i2 != i0 && i2 > i1)
                                {
                                    //System.Console.WriteLine(j + " : " + i0 + "_" + i1 + "_" + i2);
                                    j++;
                                    temp_exp.AddTerm(1.0, x_ir[i, j - 1]);
                                    temp_exp.AddTerm(-1, y_j[i0]);
                                    temp_exp.AddTerm(-1, y_j[i1]);
                                    temp_exp.AddTerm(-1, y_j[i2]);
                                    model.AddConstr(temp_exp <= 0, "c" + i0 + "_" + i1 + "_" + i2);
                                    temp_exp = 0.0;
                                }

                            }
                        }

                    }
                    j = 0;




                    //for (int r = 0; r < trial_limit; r++)
                    //{
                    //    temp_exp.AddTerm(1.0, x_ir[i, r]);
                    //    temp_exp.AddTerm(-1, y_j[i]);

                    //    for (int k1 = 0; k1 <= p; k1++)
                    //    {
                    //        temp_exp.AddTerm(-1, y_j[j]);
                    //    }


                    //}           //end of for loop for nodes
                }               //end of for loop for sample size R

                // Set objective: maximize x + y + 2 z
                //System.Console.ReadKey();

                model.Optimize();
                model.Write("model_LP_manuel" + SAA_m + ".lp");
                if (model.Status == GRB.Status.OPTIMAL)
                {
                    Console.WriteLine("Obj: " + model.Get(GRB.DoubleAttr.ObjVal));
                    solution = model.Get(GRB.DoubleAttr.ObjVal);
                    double[] dual = model.Get(GRB.DoubleAttr.Pi, model.GetConstrs());
                    //model.Get(GRB.DoubleAttr.)
                    List<int> SAA_sample_result = new List<int>(k_init);
                    StreamWriter swvarlocal = new StreamWriter("log-LPmanuel.txt");

                    for (int jj = 0; jj < N; ++jj)
                    {

                        if (y_j[jj].X > 0.001)
                        {
                            //result_set.Add(node_set[jj]);
                            //SAA_sample_result.Add(jj);
                            System.Console.WriteLine(y_j[jj].VarName + "=" + y_j[jj].X);
                            swvarlocal.WriteLine(y_j[jj].VarName + "=" + y_j[jj].X);
                            if (y_j[jj].X < 0.9)
                            {
                                System.Console.WriteLine("Fractional value found");
                                //System.Console.ReadKey();
                            }
                        }
                    }

                    for (int i = 0; i < N; i++)
                        for (int r = 0; r < sample_size; r++)
                        {
                            if (x_ir[i, r].X > 0.001)
                            {
                                //System.Console.WriteLine(x_ir[i, r].VarName + "=" + x_ir[i, r].X);
                                swvarlocal.WriteLine(x_ir[i, r].VarName + "=" + x_ir[i, r].X);
                            }
                        }
                    SAA_list.Add(SAA_sample_result);

                    GRBConstr[] cnstrs = new GRBConstr[dual.Length];
                    cnstrs = model.GetConstrs();

                    for (int i = 0; i < dual.Length; i++)
                    {
                        swvarlocal.WriteLine(cnstrs[i].ConstrName + "_" + i + " : " + dual[i]);
                    }
                    swvarlocal.Close();

                }
                else
                {
                    Console.WriteLine("No solution");
                    solution = 0;
                }

                // Dispose of model and env

                model.Dispose();
                env.Dispose();

            }
            catch (GRBException e)
            {
                Console.WriteLine("Error code: " + e.ErrorCode + ". " + e.Message);
            }


            return solution;
        }

        public static double construct_model_pipage_manuel_IP(int SAA_m, int SAA_type, int sample_size)
        {
            trial_limit = sample_size;
            System.Console.WriteLine("Constructing the MIP with Gurobi...");
            double solution = -1;
            try
            {
                GRBEnv env = new GRBEnv("mip1.log");
                GRBModel model = new GRBModel(env);
                N = 18;
                sample_size = 136;
                k_init = 6;
                int p = 3;
                //GRBVar x=new GRBVar;
                GRBVar[] y_j = new GRBVar[N];
                GRBVar[,] x_ir = new GRBVar[N, sample_size];

                System.Console.WriteLine("Creating y_i");
                for (int i = 0; i < N; i++)
                {
                    y_j[i] = model.AddVar(0.0, 1.0, 0.0, GRB.BINARY, "y_" + i);
                }

                System.Console.WriteLine("Creating x_ir");
                for (int i = 0; i < N; i++)
                    for (int r = 0; r < sample_size; r++)
                    {
                        x_ir[i, r] = model.AddVar(0.0, 1.0, 1.0, GRB.CONTINUOUS, "x_" + i + "_" + r);
                    }

                model.ModelSense = GRB.MAXIMIZE;

                //----------------------------------------------------------
                //--------------- create the constraints
                int counter = 0;
                GRBLinExpr temp_exp2;
                temp_exp2 = 0.0;
                System.Console.WriteLine("Starting the constraints... Total : " + (trial_limit * N + 1) + " constraints");
                // exactly k initial active users
                for (int i = 0; i < N; i++)
                {
                    temp_exp2.AddTerm(1.0, y_j[i]);
                }

                model.AddConstr(temp_exp2 == k_init, "constraint-y");

                //--- influence constraints x_i_r <= Sum_j (y_j)          j in all accessing nodes to i          (total of N.R constraints)

                GRBLinExpr temp_exp;

                int j = 0;

                temp_exp = 0.0;

                for (int i = 0; i < N; i++)
                {
                    int i0 = i;

                    for (int i1 = 0; i1 < N; i1++)
                    {
                        if (i1 != i0)
                        {
                            for (int i2 = 0; i2 < N; i2++)
                            {
                                if (i2 != i0 && i2 > i1)
                                {
                                    //System.Console.WriteLine(j + " : " + i0 + "_" + i1 + "_" + i2);
                                    j++;
                                    temp_exp.AddTerm(1.0, x_ir[i, j - 1]);
                                    temp_exp.AddTerm(-1, y_j[i0]);
                                    temp_exp.AddTerm(-1, y_j[i1]);
                                    temp_exp.AddTerm(-1, y_j[i2]);
                                    model.AddConstr(temp_exp <= 0, "c" + i0 + "_" + i1 + "_" + i2);
                                    temp_exp = 0.0;
                                }

                            }
                        }

                    }
                    j = 0;




                    //for (int r = 0; r < trial_limit; r++)
                    //{
                    //    temp_exp.AddTerm(1.0, x_ir[i, r]);
                    //    temp_exp.AddTerm(-1, y_j[i]);

                    //    for (int k1 = 0; k1 <= p; k1++)
                    //    {
                    //        temp_exp.AddTerm(-1, y_j[j]);
                    //    }


                    //}           //end of for loop for nodes
                }               //end of for loop for sample size R

                // Set objective: maximize x + y + 2 z
                //System.Console.ReadKey();

                model.Optimize();
                model.Write("model_IntP_manuel" + SAA_m + ".lp");
                if (model.Status == GRB.Status.OPTIMAL)
                {
                    Console.WriteLine("Obj: " + model.Get(GRB.DoubleAttr.ObjVal));
                    solution = model.Get(GRB.DoubleAttr.ObjVal);
                    StreamWriter swvarlocal = new StreamWriter("log-IPmanuel.txt");
                    List<int> SAA_sample_result = new List<int>(k_init);

                    for (int jj = 0; jj < N; ++jj)
                    {

                        if (y_j[jj].X > 0.001)
                        {
                            //result_set.Add(node_set[jj]);
                            //SAA_sample_result.Add(jj);
                            System.Console.WriteLine(y_j[jj].VarName + "=" + y_j[jj].X);
                            swvarlocal.WriteLine(y_j[jj].VarName + "=" + y_j[jj].X);
                            if (y_j[jj].X < 0.9)
                            {
                                System.Console.WriteLine("Fractional value found");
                                System.Console.ReadKey();
                            }
                        }
                    }

                    for (int i = 0; i < N; i++)
                        for (int r = 0; r < sample_size; r++)
                        {
                            if (x_ir[i, r].X > 0.001)
                            {
                                //System.Console.WriteLine(x_ir[i, r].VarName + "=" + x_ir[i, r].X);
                                swvarlocal.WriteLine(x_ir[i, r].VarName + "=" + x_ir[i, r].X);
                            }
                        }
                    SAA_list.Add(SAA_sample_result);

                    swvarlocal.Close();
                }
                else
                {
                    Console.WriteLine("No solution");
                    solution = 0;
                }

                // Dispose of model and env

                model.Dispose();
                env.Dispose();

            }
            catch (GRBException e)
            {
                Console.WriteLine("Error code: " + e.ErrorCode + ". " + e.Message);
            }


            return solution;
        }



        public static double construct_model2b_gurobi(int SAA_m, int SAA_type, int sample_size) // y_i yerine (1-y_i) koyarak oluşturulan model
        {

            trial_limit = sample_size;
            System.Console.WriteLine("Constructing the MIP with Gurobi...");
            double solution = -1;
            try
            {
                GRBEnv env = new GRBEnv("mip1.log");
                GRBModel model = new GRBModel(env);

                //GRBVar x=new GRBVar;
                GRBVar[] y_j = new GRBVar[N];
                GRBVar[,] x_ir = new GRBVar[N, sample_size];

                System.Console.WriteLine("Creating y_i");
                for (int i = 0; i < N; i++)
                {
                    y_j[i] = model.AddVar(0.0, 1.0, 0.0, GRB.BINARY, "y_" + i);
                }

                System.Console.WriteLine("Creating x_ir");
                for (int i = 0; i < N; i++)
                    for (int r = 0; r < sample_size; r++)
                    {
                        x_ir[i, r] = model.AddVar(0.0, 1.0, 1.0, GRB.CONTINUOUS, "x_" + i + "_" + r);
                    }

                model.ModelSense = GRB.MINIMIZE;

                //----------------------------------------------------------
                //--------------- create the constraints
                int counter = 0;
                GRBLinExpr temp_exp2;
                temp_exp2 = 0.0;
                System.Console.WriteLine("Starting the constraints... Total : " + (trial_limit * N + 1) + " constraints");
                // exactly k initial active users
                for (int i = 0; i < N; i++)
                {
                    temp_exp2.AddTerm(1.0, y_j[i]);
                }

                model.AddConstr(temp_exp2 == k_init, "constraint-k");

                //--- influence constraints x_i_r <= Sum_j (y_j)          j in all accessing nodes to i          (total of N.R constraints)
                string[] neigh_arr;


                GRBLinExpr temp_exp;

                int j = 0;

                temp_exp = 0.0;

                for (int r = 0; r < trial_limit; r++)
                {
                    for (int i = 0; i < N; i++)
                    {
                        temp_exp.AddTerm(1.0, x_ir[i, r]);
                        // now add the neighbours with x_j terms
                        if (SAA_tree[i, r, SAA_m] != null)
                        {
                            neigh_arr = SAA_tree[i, r, SAA_m].Split(new char[] { ',' });
                            foreach (string str in neigh_arr)   //my predecessors can activate me
                            {
                                j = Convert.ToUInt16(str);
                                {
                                    temp_exp.AddTerm(1.0, y_j[j]);
                                }
                            }
                            model.AddConstr(temp_exp >= 1, "constraint" + (counter + 1));
                            counter++;
                            temp_exp = 0.0;
                        }       //end of if for null neighbourhood
                    }           //end of for loop for nodes
                }               //end of for loop for sample size R


                model.Optimize();
                model.Write("model3.lp");
                if (model.Status == GRB.Status.OPTIMAL)
                {
                    Console.WriteLine("Obj: " + model.Get(GRB.DoubleAttr.ObjVal));
                    solution = model.Get(GRB.DoubleAttr.ObjVal);


                    List<int> SAA_sample_result = new List<int>(k_init);

                    for (int jj = 0; jj < N; ++jj)
                    {

                        if (y_j[jj].X > 0.001)
                        {
                            result_set.Add(node_set[jj]);
                            SAA_sample_result.Add((int)jj);
                            System.Console.WriteLine(y_j[jj].VarName + "=" + y_j[jj].X);
                            if (y_j[jj].X < 0.9)
                            {
                                System.Console.WriteLine("Fractional value found");
                                System.Console.ReadKey();
                            }
                        }
                    }
                    SAA_list.Add(SAA_sample_result);


                }
                else
                {
                    Console.WriteLine("No solution");
                    solution = 0;
                }

                // Dispose of model and env

                model.Dispose();
                env.Dispose();

            }
            catch (GRBException e)
            {
                Console.WriteLine("Error code: " + e.ErrorCode + ". " + e.Message);
            }


            return solution;
        }

        public static double construct_model2b_LP(int SAA_m, int SAA_type, int sample_size)
        {
            trial_limit = sample_size;
            System.Console.WriteLine("Constructing the MIP with Gurobi...");
            double solution = -1;
            try
            {
                GRBEnv env = new GRBEnv("mip1.log");
                GRBModel model = new GRBModel(env);

                //GRBVar x=new GRBVar;
                GRBVar[] y_j = new GRBVar[N];
                GRBVar[,] x_ir = new GRBVar[N, sample_size];

                System.Console.WriteLine("Creating y_i");
                for (int i = 0; i < N; i++)
                {
                    y_j[i] = model.AddVar(0.0, 1.0, 0.0, GRB.CONTINUOUS, "y_" + i);
                }

                System.Console.WriteLine("Creating x_ir");
                for (int i = 0; i < N; i++)
                    for (int r = 0; r < sample_size; r++)
                    {
                        x_ir[i, r] = model.AddVar(0.0, 1.0, 1.0, GRB.CONTINUOUS, "x_" + i + "_" + r);
                    }

                model.ModelSense = GRB.MINIMIZE;

                //----------------------------------------------------------
                //--------------- create the constraints
                int counter = 0;
                GRBLinExpr temp_exp2;
                temp_exp2 = 0.0;
                System.Console.WriteLine("Starting the constraints... Total : " + (trial_limit * N + 1) + " constraints");
                // exactly k initial active users
                for (int i = 0; i < N; i++)
                {
                    temp_exp2.AddTerm(1.0, y_j[i]);
                }

                model.AddConstr(temp_exp2 == k_init, "constraint-k");

                //--- influence constraints x_i_r <= Sum_j (y_j)          j in all accessing nodes to i          (total of N.R constraints)
                string[] neigh_arr;


                GRBLinExpr temp_exp;

                int j = 0;

                temp_exp = 0.0;

                for (int r = 0; r < trial_limit; r++)
                {
                    for (int i = 0; i < N; i++)
                    {
                        temp_exp.AddTerm(1.0, x_ir[i, r]);
                        // now add the neighbours with x_j terms
                        if (SAA_tree[i, r, SAA_m] != null)
                        {
                            neigh_arr = SAA_tree[i, r, SAA_m].Split(new char[] { ',' });
                            foreach (string str in neigh_arr)   //my predecessors can activate me
                            {
                                j = Convert.ToUInt16(str);
                                {
                                    temp_exp.AddTerm(1.0, y_j[j]);
                                }
                            }
                            model.AddConstr(temp_exp >= 1, "constraint" + (counter + 1));
                            counter++;
                            temp_exp = 0.0;
                        }       //end of if for null neighbourhood
                    }           //end of for loop for nodes
                }               //end of for loop for sample size R

                model.Optimize();
                model.Write("model3.lp");
                if (model.Status == GRB.Status.OPTIMAL)
                {
                    Console.WriteLine("Obj: " + model.Get(GRB.DoubleAttr.ObjVal));
                    solution = model.Get(GRB.DoubleAttr.ObjVal);


                    List<int> SAA_sample_result = new List<int>(k_init);

                    for (int jj = 0; jj < N; ++jj)
                    {

                        if (y_j[jj].X > 0.001)
                        {
                            result_set.Add(node_set[jj]);
                            SAA_sample_result.Add((int)jj);
                            System.Console.WriteLine(y_j[jj].VarName + "=" + y_j[jj].X);
                            if (y_j[jj].X < 0.9)
                            {
                                System.Console.WriteLine("Fractional value found");
                                //System.Console.ReadKey();
                            }
                        }
                    }


                    SAA_list.Add(SAA_sample_result);


                }
                else
                {
                    Console.WriteLine("No solution");
                    solution = 0;
                }

                // Dispose of model and env

                model.Dispose();
                env.Dispose();

            }
            catch (GRBException e)
            {
                Console.WriteLine("Error code: " + e.ErrorCode + ". " + e.Message);
            }


            return solution;
        } // y_i yerine (1-y_i) koyarak oluşturulan model

        #endregion

        public static List<int> return_UInt16_list(string str)
        {
            List<int> mylist = new List<int>();
            string[] str_arr = str.Split(new char[] { ',' });
            int item;
            for (int i = 0; i < str_arr.Length; i++)
            {
                if (str_arr[i] != "")
                {
                    item = Convert.ToUInt16(str_arr[i]);
                    mylist.Add(item);
                }
            }
            return mylist;
        }

        public static double evaluate_influence_fast(List<int> initial_set, int SAA_m, int SAA_n2, int type) //evaluates from nodeIDs not actual nodes!!!
        {
            double influence = -1;

            return influence;
        }

        public static double evaluate_influence(List<int> initial_set, int SAA_m, int SAA_n2, int type) //evaluates from nodeIDs not actual nodes!!!
        {
            int temp = 0;
            double influence = 0;
            counter_prob = 0;
            counter_prob2 = 0;
            //only_arcs = unique_arcs.Select(b =>
            //               new ArcsUInt16Weighted { Head = b.Key.Head, Tail = b.Key.Tail, Weight = b.W }).AsParallel().ToList();
            //var left_nodes_neighbours = unique_arcs.GroupBy(a => a.Key.Head).Select(a => new { Head = node_index[(int)a.Key], RefList = a.Select(b => node_index[(int)b.Key.Tail]).ToList() }).AsParallel().ToList();
            var g1 = unique_arcs.GroupBy(a => a.Key.Head).Select(a => new { TailList = a.Select(b => node_index[(int)b.Key.Tail]).ToList(), WList = a.Select(b => b.W).ToList() }).AsParallel().ToList();
            List<List<int>> arclist = new List<List<int>>();
            List<double> wlist = new List<double>();
            List<int> tails = new List<int>();
            int list_size = unique_arcs.Count;
            int head = 0;
            int tail = 0;
            Random myrand = new Random();


            for (int i = 0; i < N; i++)
                arclist.Add(new List<int>());

            for (int i = 0; i < list_size; i++)
            {
                head = node_index[(int)unique_arcs[i].Key.Head];
                tail = node_index[(int)unique_arcs[i].Key.Tail];
                arclist[head].Add(i);
                tails.Add(tail);
                wlist.Add(unique_arcs[i].W);
            }

            int temp_count = 0;
            //swtemp2 = new StreamWriter("prob2.txt");
            for (int t = 0; t < SAA_n2; t++)
            {
                if (t % 1000 == 0)
                {
                    System.Console.Write("-" + t);
                }
                if (type == 3)
                {
                    independent_cascade_sub_for_greedy(initial_set, SAA_m, t, type);
                    temp = temp + active_set.Count;
                }

                else
                //independent_cascade_sub(initial_set, SAA_m, t, type);
                {
                    temp = temp + independent_cascade_sub_fast2(initial_set, SAA_m, t, type, arclist, wlist, tails, myrand);
                    //int temp2= independent_cascade_sub_fast2(initial_set, SAA_m, t, type, arclist, wlist, tails, myrand);
                }

            }
            influence = (double)temp / SAA_n2;
            System.Console.WriteLine();
            System.Console.WriteLine("cp:" + counter_prob + "/" + counter_prob2);
            //swtemp2.Close();
            return influence;
        }


        public static int independent_cascade_sub_fast(List<int> IS, int SAA_m, int t, int type, List<List<int>> arclist, List<double> wlist, List<int> tails, Random myrand)
        {
            var vertices = new Queue<int>();
            int tail = 0;
            double prop;
            bool[] marked = new bool[N];

            foreach (int element in IS.ToList())
                vertices.Enqueue(element);

            HashSet<int> visited_nodes = new HashSet<int>();
            //            bool[] marked = new bool[N];
            while (vertices.Any())
            {
                int curVertex = vertices.Dequeue();
                visited_nodes.Add(curVertex);
                marked[curVertex] = true;
                foreach (int arc in arclist[curVertex].ToList())
                {
                    tail = tails[arc];
                    if (marked[tail] == false)
                    {
                        prop = myrand.NextDouble();
                        if (prop <= wlist[arc])
                        {
                            marked[tail] = true;
                            visited_nodes.Add(tail);
                            vertices.Enqueue(tail);
                        }
                    }
                }
            }
            return visited_nodes.Count;
        }

        public static int independent_cascade_sub_fast2(List<int> IS, int SAA_m, int t, int type, List<List<int>> arclist, List<double> wlist, List<int> tails, Random myrand)
        {
            active_set = new List<int>(IS);
            CA_set = new List<int>(IS);
            NA_set = new List<int>();
            bool[] marked = new bool[N];

            foreach (int element in IS.ToList())
                marked[element] = true;
            int curr_neigh;
            int temp_neigh_index = -1;
            double temp_arc_weight = 0;
            do
            {
                temp_neigh_index = CA_set[0];
                //swvar.WriteLine(CA_set[i]+" ("+t+")");
                foreach (int edge in arclist[temp_neigh_index].ToList())   //tüm komşuları aktifleştirmeye çalış
                {
                    curr_neigh = tails[edge];
                    if (!marked[curr_neigh]) //tabi neighbour active set içinde değilse aktifleştirmeye çalış
                    {
                        temp_arc_weight = myrand.NextDouble();
                        //swtemp2.WriteLine(temp_arc_weight);
                        if (temp_arc_weight <= wlist[edge])
                        {
                            NA_set.Add(curr_neigh);
                            marked[curr_neigh] = true;
                            counter_prob++;
                            //swvar3.WriteLine(curr_neigh + " <- act by " + temp_neigh_index + " (" + t + ") prb:" + temp_arc_weight);
                        }
                    }
                }
                CA_set.RemoveAt(0);
                active_set.AddRange(NA_set);
                CA_set.AddRange(NA_set);
                NA_set.Clear();
            } while (CA_set.Count > 0);
            return active_set.Count;
        }

        public static void independent_cascade_sub(List<int> IS, int SAA_m, int t, int type)
        {
            string[] neigh_arr;
            active_set = new List<int>(IS);
            CA_set = new List<int>(IS);
            NA_set = new List<int>();
            int curr_neigh;
            int curr_neigh_index;
            string temp_arc;

            int temp_arc_index;
            int temp_neigh_index = -1;
            int arcID = -1;
            double temp_arc_weight = 0;
            do
            {
                //foreach (int i in CA_set.ToList())
                int i = 0;
                {
                    temp_neigh_index = System.Convert.ToUInt16(CA_set[i]);
                    //swvar.WriteLine(CA_set[i]+" ("+t+")");
                    if (neigh_edge_list[temp_neigh_index] != null)
                    {
                        foreach (int edge in neigh_edge_list[temp_neigh_index])   //tüm komşuları aktifleştirmeye çalış
                        {
                            //arcID = (int)edge;
                            curr_neigh = (int)arcs_intID[edge, 1];
                            if (!active_set.Contains(curr_neigh)) //tabi neighbour active set içinde değilse aktifleştirmeye çalış
                            {
                                //temp_arc = CA_set[i].ToString() + "," + curr_neigh.ToString();
                                //if (influence_prob[CA_set[i], curr_neigh] >= prop_prob)
                                //temp_arc_index = arcID_set.IndexOf(temp_arc);
                                if (type == 1)
                                    temp_arc_weight = GetUniform();// SAA_2_prb[arcID, t];
                                //if (type == 0)
                                //    temp_arc_weight = SAA_prob[arcID, t, SAA_m];
                                if (type == 2)
                                    temp_arc_weight = GetUniform(); //SAA_2_prob[arcID, t];

                                if (type == 3)
                                    temp_arc_weight = SAA_3_prob[edge, t];

                                if (type == 4)  // for only evaluate
                                    temp_arc_weight = SAA_3_prob[edge, t];

                                if (type == 5)  // for only evaluate
                                    temp_arc_weight = SAA_3_prob_dbl[edge][t];

                                if (type == 6)  // for only evaluate
                                    temp_arc_weight = SAA_float[edge, t];

                                //swtemp2.WriteLine(temp_arc_weight);
                                counter_prob2++;
                                prop_prob = 1 - weight_set[edge];
                                if (temp_arc_weight >= prop_prob)
                                {
                                    NA_set.Add(curr_neigh);
                                    counter_prob++;
                                    //swvar3.WriteLine(curr_neigh + " <- act by " + temp_neigh_index + " (" + t + ") prb:" + temp_arc_weight);
                                }
                            }
                        }
                    }
                    CA_set.Remove(CA_set[i]);
                    foreach (int j in NA_set)
                    {
                        active_set.Add(j);
                        CA_set.Add(j);
                    }
                    NA_set.Clear();
                    i++;
                }
            } while (CA_set.Count > 0);
        }

        public static void independent_cascade_sub_for_greedy(List<int> IS, int SAA_m, int t, int type)
        {
            string[] neigh_arr;
            active_set = new List<int>(IS);
            CA_set = new List<int>(IS);
            NA_set = new List<int>();
            int curr_neigh;

            //SAA_neigh = new string[N, sample_size, SAA_M];
            //SAA_neigh[temp_neigh_index,t,SAA_m]

            int temp_neigh_index = -1;
            int arcID = -1;
            double temp_arc_weight = 0;
            do
            {
                //foreach (int i in CA_set.ToList())
                int i = 0;
                {
                    temp_neigh_index = System.Convert.ToUInt16(CA_set[i]);
                    //swvar.WriteLine(CA_set[i]+" ("+t+")");

                    if (SAA_neigh[temp_neigh_index, t, SAA_m] != null)
                    {
                        neigh_arr = SAA_neigh[temp_neigh_index, t, SAA_m].Split(new char[] { ',' });     //neighbour stringini split edelim
                        foreach (string str in neigh_arr)   //tüm komşuları aktifleştirmeye çalış
                        {
                            curr_neigh = Convert.ToUInt16(str);
                            if (!active_set.Contains(curr_neigh)) //tabi neighbour active set içinde değilse aktifleştirmeye çalış
                            {
                                NA_set.Add(curr_neigh);
                            }
                        }
                    }
                    CA_set.Remove(CA_set[i]);
                    foreach (int j in NA_set)
                    {
                        active_set.Add(j);
                        CA_set.Add(j);
                    }
                    NA_set.Clear();
                    i++;
                }
            } while (CA_set.Count > 0);
        }


        public static void only_evaluate_influence()
        {
            filename = "run_100K";
            string strIMBIP30 = ""; string strIMBIP20 = ""; string strIMBIP10 = ""; string strIMBIP5 = ""; string strIMBIPS30 = "";
            string strIMBIPS20 = ""; string strIMBIPS10 = ""; string strIMBIPS5 = ""; string strCELF30 = ""; string strCELF20 = "";
            string strCELF10 = ""; string strCELF5 = ""; string strIMM30 = ""; string strIMM20 = ""; string strIMM10 = ""; string strIMM5 = "";
            //1K
            if (filename == "run_1K")
            {
                strIMBIP30 = "20,34,40,56,67,81,101,109,143,158,159,166,173,180,191,205,212,225,227,232,235,241,254,271,281,287,288,291,303,319";
                strIMBIP20 = "20,40,67,89,101,109,143,161,166,173,191,205,225,236,271,281,287,288,291,319";
                strIMBIP10 = "40,101,109,161,166,225,236,287,288,319";
                strIMBIP5 = "101,109,161,287,288";
                strIMBIPS30 = "20,34,40,56,67,81,89,101,109,143,159,166,173,181,191,205,212,225,232,236,241,254,271,281,284,287,288,291,319,332";
                strIMBIPS20 = "20,40,56,67,89,101,109,161,166,173,191,205,225,235,271,281,287,288,291,320";
                strIMBIPS10 = "40,101,109,161,166,225,236,287,288,319";
                strIMBIPS5 = "101,109,161,287,288";
                strCELF30 = "109,287,161,288,101,225,40,319,236,166,20,89,281,291,191,67,173,205,271,56,34,144,81,241,254,212,332,83,180,198";
                strCELF20 = "109,287,161,288,101,225,40,319,236,166,20,89,281,291,191,67,173,205,271,56";
                strCELF10 = "109,287,161,288,101,225,40,319,236,166";
                strCELF5 = "109,287,161,288,101";
                strIMM30 = "109,161,101,17,143,89,67,319,40,173,166,20,235,287,281,291,191,271,205,34,241,12,251,56,254,77,7,303,212,81";
                strIMM20 = "109,17,161,101,67,143,40,319,236,89,166,20,173,287,281,291,191,34,271,205";
                strIMM10 = "109,161,17,101,67,89,143,40,319,235";
                strIMM5 = "109,161,17,101,143";
            }

            //2K
            if (filename == "run_2K")
            {
                strIMBIP30 = "10,19,20,32,40,49,56,67,72,87,95,101,143,157,165,180,190,212,232,235,250,253,263,271,281,287,308,318,319,329 ";
                strIMBIP20 = "19,20,32,40,56,67,101,143,157,165,180,190,212,235,271,281,287,308,318,329 ";
                strIMBIP10 = "20,40,101,165,180,190,235,287,318,329 ";
                strIMBIP5 = "40,101,180,235,287 ";
                strIMBIPS30 = "10,19,20,32,40,56,67,72,87,95,101,143,157,165,180,190,209,212,232,235,250,253,263,271,281,287,308,318,319,329 ";
                strIMBIPS20 = "19,20,32,40,56,67,95,101,143,157,165,180,190,212,235,250,281,287,318,329 ";
                strIMBIPS10 = "20,40,101,165,180,190,235,287,318,329 ";
                strIMBIPS5 = "101,165,180,235,287 ";
                strCELF30 = " 287,180,235,101,165,40,329,190,318,157,271,20,19,67,32,281,212,308,250,143,56,95,87,232,253,34,72,55,10,276 ";
                strCELF20 = " 287,180,235,101,165,40,329,190,318,157,271,20,19,67,32,281,212,308,250,143 ";
                strCELF10 = " 287,180,235,101,165,40,329,190,318,157 ";
                strCELF5 = " 287,180,235,101,165 ";
                strIMM30 = " 287 ,161 ,6 ,67 ,235 ,327 ,101 ,143 ,165 ,40 ,319 ,271 ,190 ,87 ,20 ,157 ,281 ,250 ,308 ,10 ,212 ,32 ,232 ,12 ,72 ,56 ,263 ,49 ,7 ,180 ";
                strIMM20 = " 287 ,161 ,17 ,143 ,67 ,327 ,235 ,101 ,40 ,165 ,318 ,89 ,190 ,271 ,20 ,281 ,212 ,56 ,32 ,250 ";
                strIMM10 = " 287 ,180 ,17 ,235 ,101 ,67 ,327 ,40 ,143 ,20 ";
                strIMM5 = " 287 ,161 ,67 ,6 ,235 ";
            }


            //5K
            if (filename == "run_5K")
            {
                strIMBIP30 = " 40 ,101,143,161,190,205,225,235,287,318,329,487,574,584,596,761,871,988,1140,1145 ";
                strIMBIP20 = " 20 ,40,101,143,161,190,205,225,235,250,287,318,329,463,487,495,574,584,596,686,695,713,760,761,845,871,905,988,1140,1145 ";
                strIMBIP10 = " 101 ,143,161,205,225,287,761,871,988,1145 ";
                strIMBIP5 = " 101 ,287,761,871,1145 ";
                strIMBIPS30 = "20,40,101,143,161,173,190,205,225,235,287,318,463,487,574,584,596,686,695,713,760,761,845,871,905,961,988,1043,1139,1145 ";
                strIMBIPS20 = "40,101,143,161,190,205,225,235,287,318,329,574,584,596,686,761,871,988,1140,1145 ";
                strIMBIPS10 = "101,161,205,225,287,574,761,871,988,1145 ";
                strIMBIPS5 = " 101,287,761,871,1145 ";
                strCELF30 = " 287,761,1145,871,101,988,161,225,143,173,574,584,190,845,235,318,40,1140,760,695,463,596,20,713,905,206,1043,707,158,271 ";
                strCELF20 = " 287,761,1145,871,101,988,161,225,143,173,574,584,190,845,235,318,40,1140,760,695 ";
                strCELF10 = " 287,761,1145,871,101,988,161,225,143,173 ";
                strCELF5 = " 287,761,1145,871,101 ";
                strIMM30 = " 287 ,761 ,870 ,1145 ,329 ,988 ,205 ,101 ,143 ,17 ,580 ,602 ,89 ,575 ,161 ,40 ,318 ,67 ,20 ,190 ,235 ,596 ,686 ,271 ,845 ,487 ,1140 ,905 ,760 ,630 ";
                strIMM20 = " 287 ,761 ,870 ,1145 ,329 ,101 ,988 ,205 ,143 ,17 ,602 ,161 ,89 ,580 ,575 ,67 ,686 ,271 ,190 ,1140 ";
                strIMM10 = " 287 ,761 ,870 ,1145 ,329 ,988 ,101 ,205 ,143 ,17 ";
                strIMM5 = " 287 ,761 ,870 ,1145 ,329 ";
            }

            //10K
            if (filename == "run_10K")
            {
                strIMBIP30 = " 101 ,161,287,487,575,760,869,988,1068,1145,1220,1284,1300,1468,1613,1625,1677,1738,1762,1804,1951,2054,2106,2452,2665,2755,2808,2852,2864,3040 ";
                strIMBIP20 = " 287 ,760,869,988,1068,1145,1220,1284,1300,1468,1613,1677,1738,1762,1804,2054,2665,2809,2864,3040 ";
                strIMBIP10 = " 287 ,760,1284,1300,1677,1738,1762,1804,2809,2864 ";
                strIMBIP5 = " 287 ,760,1677,1804,2809 ";
                strIMBIPS30 = " 101,287,487,575,584,760,869,988,1068,1145,1220,1284,1300,1468,1613,1625,1677,1738,1762,1804,1951,2054,2106,2665,2755,2809,2852,2864,3000,3040 ";
                strIMBIPS20 = " 287,760,869,988,1068,1145,1284,1300,1468,1613,1625,1677,1738,1762,1804,2054,2665,2808,2864,3040 ";
                strIMBIPS10 = " 109,760,1284,1300,1677,1738,1762,1804,2809,2864 ";
                strIMBIPS5 = " 288,760,1677,1804,2808 ";
                strCELF30 = " 287,760,1677,1804,2809,2864,1762,1738,1300,1284,2665,1068,869,1145,1468,1613,3040,2054,2852,1220,988,1951,1625,2106,2755,578,2452,487,3000,2597 ";
                strCELF20 = " 287,760,1677,1804,2809,2864,1762,1738,1300,1284,2665,1068,869,1145,1468,1613,3040,2054,2852,1220 ";
                strCELF10 = " 287,760,1677,1804,2809,2864,1762,1738,1300,1284 ";
                strCELF5 = " 287,760,1677,1804,2809 ";
                strIMM30 = " 288 ,760 ,1677 ,1804 ,1300 ,1738 ,2809 ,2864 ,870 ,1068 ,1762 ,1284 ,2665 ,1613 ,1468 ,2054 ,575 ,1145 ,988 ,2451 ,1220 ,3040 ,2852 ,327 ,1951 ,1625 ,604 ,2105 ,1039 ,2755 ";
                strIMM20 = " 287 ,760 ,1677 ,1804 ,1300 ,1738 ,1227 ,2809 ,1068 ,870 ,1762 ,1284 ,2665 ,1468 ,1613 ,575 ,1145 ,2054 ,988 ,3040 ";
                strIMM10 = " 288 ,760 ,1677 ,1804 ,1300 ,1738 ,2809 ,2864 ,1068 ,870 ";
                strIMM5 = " 288 ,760 ,1677 ,1804 ,1300 ";
            }

            //20K
            if (filename == "run_20K")
            {
                strIMBIP30 = " 288 ,763,1227,1284,1300,1676,1762,1802,2106,2184,2808,3104,3205,3228,3301,3660,3697,3846,3888,3982,4336,4486,4821,5104,5490,5582,5670,5678,5823,5835 ";
                strIMBIP20 = " 288 ,763,1227,1677,1802,2808,3104,3227,3301,3660,3697,3888,4336,4486,4821,5104,5490,5582,5678,5823 ";
                strIMBIP10 = " 288 ,763,1677,1802,3104,3227,3301,3888,4486,4832 ";
                strIMBIP5 = " 288 ,763,3301,4486,4832 ";
                strIMBIPS30 = " 288,763,1227,1284,1300,1677,1762,1804,2106,2184,2808,3104,3203,3227,3301,3660,3697,3846,3888,3982,4336,4486,4815,4821,5104,5490,5582,5670,5678,5834 ";
                strIMBIPS20 = " 288,760,1227,1300,1676,1802,2808,3104,3227,3301,3660,3697,3888,4336,4486,4821,5104,5490,5581,5678 ";
                strIMBIPS10 = " 109,761,1677,1802,3104,3227,3301,3888,4486,4832 ";
                strIMBIPS5 = " 287,763,3301,4486,4832 ";
                strCELF30 = " 287,763,4832,3301,3104,4486,3888,1676,1802,3227,5677,4336,3697,1227,2808,5581,5489,3660,2106,5822,5834,3205,1300,1284,5103,1762,3982,5669,2184,4366 ";
                strCELF20 = " 287,763,4832,3301,3104,4486,3888,1676,1802,3227,5677,4336,3697,1227,2808,5581,5489,3660,2106,5822 ";
                strCELF10 = " 287,763,4832,3301,3104,4486,3888,1676,1802,3227 ";
                strCELF5 = " 287,763,4832,3301,3104 ";
                strIMM30 = " 287 ,763 ,4832 ,3301 ,4486 ,3104 ,3888 ,1676 ,5570 ,1300 ,5835 ,1802 ,4336 ,3697 ,1227 ,1738 ,3660 ,3982 ,2808 ,5490 ,1612 ,5582 ,2106 ,870 ,5823 ,3203 ,1762 ,5104 ,5670 ,3228 ";
                strIMM20 = " 287 ,763 ,4832 ,3301 ,3104 ,4486 ,3888 ,1676 ,5570 ,3227 ,1802 ,4336 ,3697 ,1227 ,1300 ,3982 ,1739 ,3660 ,1612 ,2808 ";
                strIMM10 = " 109 ,763 ,4832 ,3302 ,4486 ,3104 ,3888 ,1676 ,5570 ,1802 ";
                strIMM5 = " 287 ,763 ,4832 ,3302 ,3104 ";
            }

            //50K
            if (filename == "run_50K")
            {
                strIMBIP30 = " 287 ,760,1676,1802,2038,2721,3104,3227,3301,3660,3697,3846,3888,4336,4486,4697,4821,5193,5678,6157,6723,7039,7720,8505,9619,10040,10580,10713,11935,12016 ";
                strIMBIP20 = " 287 ,760,922,1676,3104,3227,3302,3888,4486,4697,5570,6723,7039,7720,8505,9619,10040,10580,10713,12016 ";
                strIMBIP10 = " 287 ,760,922,3104,3302,7720,10040,10580,10713,12016 ";
                strIMBIP5 = " 287 ,760,922,7720,12016 ";
                strIMBIPS30 = " 287,760,1676,1802,2038,2721,3104,3203,3227,3302,3663,3697,3846,3888,4336,4486,4697,4821,5570,5979,6157,7039,7720,8505,9619,10040,10580,10713,11935,12016 ";
                strIMBIPS20 = " 287,760,1676,2721,3104,3227,3302,3888,4486,4821,5104,5570,7039,7720,8505,9619,10040,10580,11089,12016 ";
                strIMBIPS10 = " 287,760,922,3104,3302,7720,10040,10580,11089,12016 ";
                strIMBIPS5 = " 287,760,4832,7720,12016 ";
                strCELF30 = " 6028,7719,12015,287,11088,760,4832,10039,10579,7038,3104,3302,4486,3888,3227,1676,8504,9618,5569,6722,11934,1802,3697,4336,4697,3660,6175,2809,5192,6156 ";
                strCELF20 = " 6028,7719,12015,287,11088,760,4832,10039,10579,7038,3104,3302,4486,3888,3227,1676,8504,9618,5569,6722 ";
                strCELF10 = " 6028,7719,12015,287,11088,760,4832,10039,10579,7038 ";
                strCELF5 = " 6028,7719,12015,287,11088 ";
                strIMM30 = " 5104 ,7720 ,12016 ,287 ,10713 ,760 ,10040 ,2038 ,10579 ,3104 ,7039 ,3567 ,3888 ,4697 ,8505 ,1676 ,3227 ,5979 ,5193 ,5570 ,9619 ,2537 ,3697 ,6971 ,1802 ,11935 ,3660 ,4336 ,4821 ,8958 ";
                strIMM20 = " 5104 ,7720 ,12016 ,10713 ,287 ,760 ,10040 ,2038 ,10580 ,3104 ,7039 ,3567 ,3888 ,8505 ,4697 ,1676 ,5979 ,3227 ,9619 ,2537 ";
                strIMM10 = " 5104 ,7720 ,12016 ,10713 ,287 ,760 ,10040 ,10580 ,2038 ,3104 ";
                strIMM5 = " 5104 ,7720 ,12016 ,10713 ,109 ";
            }

            //100K
            if (filename == "run_100K")
            {
                strIMBIPS10 = "15313,6600,7721,11088,13680,14021,13907,3301,12728,762,16776,10580,18634,7038,12248,10041,5192,109,881,3227";
                strIMM10 = "3301,12728,11727,7721,109,762,11088,13680,15313,12247,14020,10040,10580,13907,12625,16778,6894,3227,881,16822";
            }

            string[] str_IMBIP;
            string[] str_IMBIPS;
            string[] str_CELF;
            string[] str_IMM;
            int size = 1;
            str_IMBIP = new string[size];
            str_IMBIPS = new string[size];
            str_CELF = new string[size];
            str_IMM = new string[size];

            if (filename == "gnutella")
            {

                str_IMBIP[0] = "314,547,4496,5150,1591,1655,7050,2056,2082,2416,3109,3427,3556,3761,4057,4097,5067,8308,5598,5617,6101,6194,6784,7553,8292,9134,9628,10043,10231,10632";
                str_IMBIP[1] = "4657,314,4496,798,1252,1655,2082,2416,3109,3132,3355,3427,3556,3761,4057,4097,8308,5478,5598,5617,6101,6953,8292,9134,9628,9798,10043,10231,10649";
                str_IMBIP[2] = "2537,4657,314,4496,753,1655,2416,3109,3132,3427,3556,3581,3761,4057,4097,8308,5478,5598,5617,6101,6687,7325,7596,9134,9701,10043,10231,10368";
                str_IMBIP[3] = "314,4496,753,5150,1655,2082,2416,3109,3132,3334,3427,3556,3581,3761,4057,4097,8308,5598,5617,6101,6687,9134,9628,10043,10231,10368,10530";
                str_IMBIP[4] = "2537,4657,314,4496,753,1252,1655,2416,2882,3109,3132,3427,3556,3581,4057,4097,8308,5598,5617,6101,6515,7553,9134,10043,10231,10649";
                str_IMBIP[5] = "314,4496,753,846,1655,2416,3109,3132,3427,3556,3761,4057,4097,8308,5478,5598,5617,6101,6687,9134,9276,9628,9892,10043,10231";
                str_IMBIP[6] = "2537,4657,314,4496,1619,1655,2416,3109,3132,3427,3556,3761,4057,4097,8308,5478,5598,5617,6101,6687,9134,9701,10043,10231";
                str_IMBIP[7] = "4657,314,4496,753,5150,1655,2416,3109,3132,3427,3556,3761,4057,4097,8308,5598,5617,6101,6687,7325,9134,10043,10231";
                str_IMBIP[8] = "314,4496,753,846,5150,1655,2416,2882,3109,3132,3427,3556,3761,4057,4097,8308,5598,5617,6101,9134,10043,10231";
                str_IMBIP[9] = "314,4496,753,1655,2416,3109,3132,3556,3581,3761,4057,4097,8308,5598,5617,6101,9134,9628,9701,10043,10231";
                str_IMBIP[10] = "314,4496,1430,1655,2082,2416,3109,3427,3556,3761,4057,4097,8308,5598,5617,6101,6687,9134,10043,10231";
                str_IMBIP[11] = "4657,314,4496,1655,2416,3109,3132,3427,3556,3761,4057,4097,8308,5598,5617,6101,9134,10043,10231";
                str_IMBIP[12] = "314,4496,753,1655,2416,3109,3132,3556,3761,4057,4097,8308,5598,5617,6101,9134,10043,10231";
                str_IMBIP[13] = "314,4496,1655,2416,3109,3427,3556,3761,4057,4097,8308,5598,5617,6101,9134,10043,10231";
                str_IMBIP[14] = "314,4496,1655,2416,3109,3427,3556,3761,4057,4097,8308,5598,5617,6101,9134,10043";
                str_IMBIP[15] = "314,4496,1655,2416,3109,3556,3761,4057,4097,8308,5598,5617,6101,9134,10043";
                str_IMBIP[16] = "314,4496,1655,2416,3109,3556,4057,4097,8308,5598,5617,6101,9134,10043";
                str_IMBIP[17] = "314,4496,1655,2416,3109,3556,4097,8308,5598,5617,6101,9134,10043";
                str_IMBIP[18] = "4496,1655,2416,3109,3556,4097,8308,5598,5617,6101,9134,10043";
                str_IMBIP[19] = "4496,1655,2416,3109,4097,8308,5598,5617,6101,9134,10043";
                str_IMBIP[20] = "4496,1655,2416,3109,8308,5598,5617,6101,9134,10043";
                str_IMBIP[21] = "1655,2416,3109,8308,5598,5617,6101,9134,10043";
                str_IMBIP[22] = "1655,2416,3109,8308,5617,6101,9134,10043";
                str_IMBIP[23] = "1655,2416,3109,5617,6101,9134,10043";
                str_IMBIP[24] = "1655,2416,3109,5617,6101,9134";
                str_IMBIP[25] = "1655,2416,3109,5617,9134";
                str_IMBIP[26] = "1655,2416,3109,9134";
                str_IMBIP[27] = "1655,2416,3109";
                str_IMBIP[28] = "1655,3109";
                str_IMBIP[29] = "3109";

                str_IMBIPS[0] = "2537,4657,314,427,4496,1655,7050,2385,2416,3109,3132,3427,3556,3761,4057,4097,8308,5478,5598,5617,6101,6687,6937,8089,9134,9892,10043,10231,10649,10809";
                str_IMBIPS[1] = "2537,158,314,4496,753,1495,5150,1655,2416,3109,3132,3427,3556,3761,4057,4097,8308,5478,5598,5617,6101,6687,9134,9701,9892,10043,10231,10310,10368";
                str_IMBIPS[2] = "2537,4657,314,4496,753,1655,2416,3109,3132,3427,3556,3581,3761,4057,4097,8308,5478,5598,5617,6101,6687,7325,7596,9134,9701,10043,10231,10368";
                str_IMBIPS[3] = "314,4496,753,5150,1655,2082,2416,3109,3132,3334,3427,3556,3581,3761,4057,4097,8308,5598,5617,6101,6687,9134,9628,10043,10231,10368,10530";
                str_IMBIPS[4] = "314,4496,753,920,1252,1655,7050,2082,2416,2461,3109,3427,3556,3761,4057,4097,8308,5478,5598,5617,6101,8292,9134,9892,10043,10231";
                str_IMBIPS[5] = "4657,314,4496,753,846,5150,1655,2416,3109,3334,3427,3556,3761,4057,4097,8308,5478,5598,5617,6101,7111,9134,10043,10231,10649";
                str_IMBIPS[6] = "314,4496,753,1655,2082,2292,2416,3109,3132,3427,3556,3581,3761,4057,4097,8308,5598,5617,6101,9134,9628,10043,10231,10368";
                str_IMBIPS[7] = "4657,314,4496,753,5150,1655,2416,3109,3132,3427,3556,3761,4057,4097,8308,5598,5617,6101,6687,7325,9134,10043,10231";
                str_IMBIPS[8] = "314,4496,1655,2416,3109,3132,3355,3427,3556,3761,4057,4097,8308,5478,5598,5617,6101,6687,9134,10043,10231,10368";
                str_IMBIPS[9] = "314,4496,753,1495,1655,2416,3109,3132,3556,3761,4057,4097,8308,5598,5617,6101,6687,9134,9892,10043,10231";
                str_IMBIPS[10] = "314,4496,1430,1655,2082,2416,3109,3427,3556,3761,4057,4097,8308,5598,5617,6101,6687,9134,10043,10231";
                str_IMBIPS[11] = "314,4496,1655,2416,3109,3132,3427,3556,3761,4057,4097,8308,5598,5617,6101,9134,10043,10231,10368";
                str_IMBIPS[12] = "314,4496,753,1655,2416,3109,3427,3556,3761,4057,4097,8308,5598,5617,6101,9134,10043,10231";
                str_IMBIPS[13] = "314,4496,1655,2416,3109,3132,3556,3761,4057,4097,8308,5598,5617,6101,9134,10043,10231";
                str_IMBIPS[14] = "314,4496,1655,2416,3109,3556,3761,4057,4097,8308,5598,5617,6101,9134,10043,10231";
                str_IMBIPS[15] = "314,4496,1655,2416,3109,3556,3761,4057,4097,8308,5598,5617,6101,9134,10043";
                str_IMBIPS[16] = "314,4496,1655,2416,3109,3556,3761,4097,8308,5598,5617,6101,9134,10043";
                str_IMBIPS[17] = "314,4496,1655,2416,3109,3556,4097,8308,5598,5617,6101,9134,10043";
                str_IMBIPS[18] = "4496,1655,2416,3109,3556,4097,8308,5598,5617,6101,9134,10043";
                str_IMBIPS[19] = "4496,1655,2416,3109,4097,8308,5598,5617,6101,9134,10043";
                str_IMBIPS[20] = "4496,1655,2416,3109,8308,5598,5617,6101,9134,10043";
                str_IMBIPS[21] = "1655,2416,3109,8308,5598,5617,6101,9134,10043";
                str_IMBIPS[22] = "1655,2416,3109,8308,5617,6101,9134,10043";
                str_IMBIPS[23] = "1655,2416,3109,5617,6101,9134,10043";
                str_IMBIPS[24] = "1655,2416,3109,5617,6101,9134";
                str_IMBIPS[25] = "1655,2416,3109,5617,9134";
                str_IMBIPS[26] = "1655,2416,3109,9134";
                str_IMBIPS[27] = "1655,2416,3109";
                str_IMBIPS[28] = "2416,3109";
                str_IMBIPS[29] = "3109";
                str_CELF[0] = "3109 , 1655 , 2416 , 9134 , 5617 , 6101 , 10043 , 4496 , 5598 , 8308 , 4097 , 3556 , 314 , 3761 , 10231 , 4057 , 4657 , 3427 , 5150 , 5241 , 7325 , 6687 , 10368 , 4592 , 2082 , 9965 , 768 , 1762 , 1890 , 8292";
                str_CELF[1] = "3109 , 1655 , 2416 , 9134 , 5617 , 6101 , 10043 , 4496 , 5598 , 8308 , 4097 , 3556 , 314 , 3761 , 10231 , 4057 , 4657 , 3427 , 5150 , 5241 , 7325 , 6687 , 10368 , 4592 , 2082 , 9965 , 768 , 1762 , 1890";
                str_CELF[2] = "3109 , 1655 , 2416 , 9134 , 5617 , 6101 , 10043 , 4496 , 5598 , 8308 , 4097 , 3556 , 314 , 3761 , 10231 , 4057 , 4657 , 3427 , 5150 , 5241 , 7325 , 6687 , 10368 , 4592 , 2082 , 9965 , 768 , 1762";
                str_CELF[3] = "3109 , 1655 , 2416 , 9134 , 5617 , 6101 , 10043 , 4496 , 5598 , 8308 , 4097 , 3556 , 314 , 3761 , 10231 , 4057 , 4657 , 3427 , 5150 , 5241 , 7325 , 6687 , 10368 , 4592 , 2082 , 9965 , 768";
                str_CELF[4] = "3109 , 1655 , 2416 , 9134 , 5617 , 6101 , 10043 , 4496 , 5598 , 8308 , 4097 , 3556 , 314 , 3761 , 10231 , 4057 , 4657 , 3427 , 5150 , 5241 , 7325 , 6687 , 10368 , 4592 , 2082 , 9965";
                str_CELF[5] = "3109 , 1655 , 2416 , 9134 , 5617 , 6101 , 10043 , 4496 , 5598 , 8308 , 4097 , 3556 , 314 , 3761 , 10231 , 4057 , 4657 , 3427 , 5150 , 5241 , 7325 , 6687 , 10368 , 4592 , 2082";
                str_CELF[6] = "3109 , 1655 , 2416 , 9134 , 5617 , 6101 , 10043 , 4496 , 5598 , 8308 , 4097 , 3556 , 314 , 3761 , 10231 , 4057 , 4657 , 3427 , 5150 , 5241 , 7325 , 6687 , 10368 , 4592";
                str_CELF[7] = "3109 , 1655 , 2416 , 9134 , 5617 , 6101 , 10043 , 4496 , 5598 , 8308 , 4097 , 3556 , 314 , 3761 , 10231 , 4057 , 4657 , 3427 , 5150 , 5241 , 7325 , 6687 , 10368";
                str_CELF[8] = "3109 , 1655 , 2416 , 9134 , 5617 , 6101 , 10043 , 4496 , 5598 , 8308 , 4097 , 3556 , 314 , 3761 , 10231 , 4057 , 4657 , 3427 , 5150 , 5241 , 7325 , 6687";
                str_CELF[9] = "3109 , 1655 , 2416 , 9134 , 5617 , 6101 , 10043 , 4496 , 5598 , 8308 , 4097 , 3556 , 314 , 3761 , 10231 , 4057 , 4657 , 3427 , 5150 , 5241 , 7325";
                str_CELF[10] = "3109 , 1655 , 2416 , 9134 , 5617 , 6101 , 10043 , 4496 , 5598 , 8308 , 4097 , 3556 , 314 , 3761 , 10231 , 4057 , 4657 , 3427 , 5150 , 5241";
                str_CELF[11] = "3109 , 1655 , 2416 , 9134 , 5617 , 6101 , 10043 , 4496 , 5598 , 8308 , 4097 , 3556 , 314 , 3761 , 10231 , 4057 , 4657 , 3427 , 5150";
                str_CELF[12] = "3109 , 1655 , 2416 , 9134 , 5617 , 6101 , 10043 , 4496 , 5598 , 8308 , 4097 , 3556 , 314 , 3761 , 10231 , 4057 , 4657 , 3427";
                str_CELF[13] = "3109 , 1655 , 2416 , 9134 , 5617 , 6101 , 10043 , 4496 , 5598 , 8308 , 4097 , 3556 , 314 , 3761 , 10231 , 4057 , 4657";
                str_CELF[14] = "3109 , 1655 , 2416 , 9134 , 5617 , 6101 , 10043 , 4496 , 5598 , 8308 , 4097 , 3556 , 314 , 3761 , 10231 , 4057";
                str_CELF[15] = "3109 , 1655 , 2416 , 9134 , 5617 , 6101 , 10043 , 4496 , 5598 , 8308 , 4097 , 3556 , 314 , 3761 , 10231";
                str_CELF[16] = "3109 , 1655 , 2416 , 9134 , 5617 , 6101 , 10043 , 4496 , 5598 , 8308 , 4097 , 3556 , 314 , 3761";
                str_CELF[17] = "3109 , 1655 , 2416 , 9134 , 5617 , 6101 , 10043 , 4496 , 5598 , 8308 , 4097 , 3556 , 314";
                str_CELF[18] = "3109 , 1655 , 2416 , 9134 , 5617 , 6101 , 10043 , 4496 , 5598 , 8308 , 4097 , 3556";
                str_CELF[19] = "3109 , 1655 , 2416 , 9134 , 5617 , 6101 , 10043 , 4496 , 5598 , 8308 , 4097";
                str_CELF[20] = "3109 , 1655 , 2416 , 9134 , 5617 , 6101 , 10043 , 4496 , 5598 , 8308";
                str_CELF[21] = "3109 , 1655 , 2416 , 9134 , 5617 , 6101 , 10043 , 4496 , 5598";
                str_CELF[22] = "3109 , 1655 , 2416 , 9134 , 5617 , 6101 , 10043 , 4496";
                str_CELF[23] = "3109 , 1655 , 2416 , 9134 , 5617 , 6101 , 10043";
                str_CELF[24] = "3109 , 1655 , 2416 , 9134 , 5617 , 6101";
                str_CELF[25] = "3109 , 1655 , 2416 , 9134 , 5617";
                str_CELF[26] = "3109 , 1655 , 2416 , 9134";
                str_CELF[27] = "3109 , 1655 , 2416";
                str_CELF[28] = "3109 , 1655";
                str_CELF[29] = "3109";


                str_IMM[0] = "3109, 1655, 2416, 9134, 5617, 6101, 5598, 10043, 8308, 4496, 4097, 3556, 314, 4057, 3761, 10231, 3132, 3427, 753, 2082, 9701, 5150, 5478, 10368, 7553, 4657, 6687, 6053, 2537, 2882";
                str_IMM[1] = "3109, 1655, 2416, 9134, 5617, 6101, 10043, 5598, 8308, 4496, 4097, 3556, 314, 10231, 3761, 4057, 3132, 6687, 3427, 753, 4657, 3334, 2082, 9311, 5150, 9701, 9628, 9892, 3355";
                str_IMM[2] = "3109, 1655, 9134, 2416, 5617, 6101, 5598, 10043, 8308, 4496, 4097, 314, 3556, 3761, 4057, 10231, 3132, 6687, 3427, 5478, 10649, 753, 8089, 6784, 5150, 3355, 3334, 2082";
                str_IMM[3] = "3109, 2416, 9134, 1655, 5617, 6101, 10043, 4097, 8308, 4496, 3556, 5598, 314, 3761, 10231, 4057, 3132, 753, 3427, 5478, 6687, 5150, 920, 10368, 8292, 3581, 9701";
                str_IMM[4] = "3109, 1655, 9134, 2416, 5617, 6101, 10043, 5598, 3556, 4496, 4097, 8308, 3761, 314, 4057, 10231, 3427, 753, 3132, 2882, 5478, 10649, 4657, 2082, 3334, 3581";
                str_IMM[5] = "3109, 2416, 1655, 9134, 5617, 6101, 4496, 10043, 4097, 5598, 8308, 3556, 314, 4057, 3761, 10231, 3427, 3334, 753, 3355, 5150, 920, 9720, 6687, 2082";
                str_IMM[6] = "3109, 1655, 2416, 5617, 9134, 6101, 10043, 8308, 4097, 5598, 4496, 3556, 314, 3761, 4057, 10231, 920, 753, 3427, 8292, 5478, 2082, 2882, 6687";
                str_IMM[7] = "3109, 5617, 1655, 2416, 9134, 6101, 10043, 5598, 8308, 4097, 4496, 3556, 314, 4057, 3761, 10231, 6687, 753, 3427, 920, 7553, 9892, 8292";
                str_IMM[8] = "3109, 1655, 2416, 9134, 5617, 6101, 10043, 5598, 8308, 4496, 3556, 4097, 314, 4057, 3761, 10231, 2082, 3427, 5150, 5478, 10368, 3355";
                str_IMM[9] = "3109, 1655, 9134, 2416, 5617, 6101, 8308, 10043, 4097, 5598, 4496, 3556, 314, 3761, 4057, 10231, 5150, 3132, 5478, 10368, 6687";
                str_IMM[10] = "3109, 9134, 2416, 1655, 5617, 6101, 10043, 5598, 4496, 8308, 3556, 4097, 314, 4057, 3761, 10231, 3427, 5150, 920, 4657";
                str_IMM[11] = "3109, 1655, 2416, 5617, 9134, 6101, 10043, 8308, 4496, 5598, 4097, 314, 3556, 3761, 4057, 6687, 10231, 3132, 753";
                str_IMM[12] = "3109, 1655, 2416, 9134, 5617, 6101, 10043, 8308, 4496, 5598, 3556, 4097, 314, 3761, 4057, 10231, 2082, 753";
                str_IMM[13] = "3109, 2416, 1655, 9134, 5617, 6101, 10043, 4496, 5598, 8308, 4097, 314, 3556, 3761, 4057, 10231, 753";
                str_IMM[14] = "3109, 2416, 5617, 1655, 9134, 6101, 8308, 5598, 10043, 3556, 4097, 4496, 314, 3761, 4057, 753";
                str_IMM[15] = "3109, 9134, 2416, 1655, 5617, 6101, 10043, 5598, 8308, 4097, 4496, 314, 3556, 10231, 3761";
                str_IMM[16] = "3109, 1655, 2416, 9134, 5617, 6101, 10043, 5598, 8308, 4496, 3556, 314, 4097, 4057";
                str_IMM[17] = "3109, 9134, 1655, 2416, 5617, 6101, 10043, 5598, 4496, 8308, 4097, 314, 3556";
                str_IMM[18] = "3109, 1655, 2416, 9134, 5617, 6101, 10043, 5598, 8308, 4097, 4496, 314";
                str_IMM[19] = "3109, 2416, 1655, 9134, 5617, 6101, 10043, 8308, 5598, 3556, 4496";
                str_IMM[20] = "3109, 9134, 1655, 5617, 2416, 6101, 10043, 5598, 8308, 4496";
                str_IMM[21] = "3109, 1655, 2416, 9134, 5617, 6101, 10043, 5598, 8308";
                str_IMM[22] = "3109, 1655, 2416, 9134, 5617, 6101, 10043, 5598";
                str_IMM[23] = "3109, 1655, 2416, 9134, 5617, 6101, 5598";
                str_IMM[24] = "3109, 5617, 1655, 2416, 9134, 6101";
                str_IMM[25] = "3109, 2416, 9134, 5617, 1655";
                str_IMM[26] = "3109, 1655, 2416, 9134";
                str_IMM[27] = "3109, 9134, 2416";
                str_IMM[28] = "3109, 1655";
                str_IMM[29] = "3109";


            }


            if (filename == "facebook")
            {
                str_IMBIP[0] = "0,21,107,136,348,1684,1912,353,366,376,896,916,917,925,946,966,1577,1926,370,3437,686,1941,2661,2664,2669,2679,2716,2742,1917,1929";
                str_IMBIP[1] = "0,107,136,348,414,1684,1912,366,376,483,896,916,917,925,946,966,1577,1926,3437,686,1941,2664,2669,2719,2730,2742,2754,1917,1946";
                str_IMBIP[2] = "0,107,136,348,414,1684,1912,353,366,376,896,916,917,925,946,1577,1926,3437,686,2661,2664,2669,2716,2742,2754,1917,1938,1943";
                str_IMBIP[3] = "0,107,136,348,414,1684,1912,366,376,896,916,917,925,946,1577,1926,370,3437,686,1941,2661,2664,2679,2730,2742,1917,1929";
                str_IMBIP[4] = "0,107,136,348,414,1684,1912,366,376,896,916,917,925,946,1577,1926,3437,686,1941,2661,2664,2669,2716,2742,1917,1929";
                str_IMBIP[5] = "0,107,136,348,414,1684,1912,366,376,896,916,917,925,946,1577,1926,3437,686,1941,2664,2669,2719,2742,1917,1962";
                str_IMBIP[6] = "0,107,136,348,414,1684,1912,366,376,896,916,917,925,946,1577,3437,686,1941,2661,2669,2742,2754,1917,1946";
                str_IMBIP[7] = "0,107,348,414,1684,1912,366,376,896,916,917,925,946,1577,1926,3437,686,1941,2661,2669,2742,2754,1917";
                str_IMBIP[8] = "0,107,348,414,1684,1912,353,376,896,916,917,925,946,1577,1926,3437,686,2661,2664,2669,1938,1962";
                str_IMBIP[9] = "0,107,348,414,1684,1912,353,366,896,916,917,925,946,1577,1926,3437,686,1941,2661,2669,1917";
                str_IMBIP[10] = "0,107,348,1684,1912,363,376,896,916,917,925,946,1577,3437,686,1941,2664,2669,2742,1962";
                str_IMBIP[11] = "0,107,136,348,414,1684,1912,366,896,916,917,925,1577,3437,686,1941,2661,2669,1917";
                str_IMBIP[12] = "0,107,348,414,1684,1912,376,896,916,917,925,1577,3437,686,1941,2661,2669,1946";
                str_IMBIP[13] = "0,107,348,1684,1912,363,376,917,925,946,1577,3437,686,1941,2669,2742,1917";
                str_IMBIP[14] = "0,107,348,1684,1912,376,896,925,946,1577,3437,686,1941,2661,2664,1917";
                str_IMBIP[15] = "0,107,348,1684,1912,376,916,917,946,1577,3437,686,1941,2669,1917";
                str_IMBIP[16] = "0,107,348,1684,1912,376,916,917,946,3437,686,1941,2669,1917";
                str_IMBIP[17] = "0,107,348,1684,1912,376,925,946,3437,686,1941,2669,1917";
                str_IMBIP[18] = "0,107,348,1684,1912,916,946,1577,3437,686,2669,1938";
                str_IMBIP[19] = "0,107,348,1684,1912,376,925,3437,686,1941,1917";
                str_IMBIP[20] = "0,107,348,1684,1912,946,3437,686,1941,1917";
                str_IMBIP[21] = "0,107,348,1684,1912,946,1577,3437,1917";
                str_IMBIP[22] = "0,107,348,1684,1912,946,3437,1941";
                str_IMBIP[23] = "0,107,348,1684,1912,3437,1941";
                str_IMBIP[24] = "107,348,1684,1912,3437,1941";
                str_IMBIP[25] = "107,348,1684,1912,3437";
                str_IMBIP[26] = "107,1684,1912,3437";
                str_IMBIP[27] = "107,1684,1912";
                str_IMBIP[28] = "107,1912";
                str_IMBIP[29] = "107";

                str_IMBIPS[0] = "0,67,107,136,348,1684,1912,363,366,896,916,917,925,946,947,1926,370,3437,686,1920,1941,2661,2664,2679,2694,2719,2742,1917,1918,1946";
                str_IMBIPS[1] = "0,107,136,348,414,1684,1912,353,376,896,916,917,925,946,953,1577,1926,370,3437,686,1941,2661,2664,2676,2679,2742,1917,1946,1962";
                str_IMBIPS[2] = "0,107,136,348,414,1684,1912,353,366,896,916,917,925,946,966,1577,373,3437,686,1941,2661,2669,2716,2742,2754,1917,1943,1985";
                str_IMBIPS[3] = "0,21,107,348,414,1684,1912,376,896,916,917,925,960,966,1577,1926,370,3437,686,2661,2664,2679,2730,2742,1917,1938,1962";
                str_IMBIPS[4] = "0,107,136,348,414,1684,1912,366,376,896,916,917,925,946,1577,1926,3437,686,1941,2661,2664,2676,2742,1917,1943,1946";
                str_IMBIPS[5] = "0,107,136,348,414,1684,1912,366,376,896,916,917,925,946,1926,3437,686,1941,2664,2716,2730,2742,2754,1938,1985";
                str_IMBIPS[6] = "0,21,107,348,1684,1912,363,366,896,916,917,925,946,1926,373,3437,686,1920,1941,2669,2716,2719,1938,1962";
                str_IMBIPS[7] = "0,107,136,348,1684,1912,353,363,896,916,917,946,1577,370,3437,686,1941,2669,2674,2694,2742,1943,1946";
                str_IMBIPS[8] = "0,107,348,1684,1912,363,376,896,916,917,921,946,1577,373,3437,686,1941,2664,2716,2742,1917,1943";
                str_IMBIPS[9] = "0,107,136,348,1684,1912,376,896,916,917,925,946,373,3437,686,1941,2661,2669,2742,1943,1964";
                str_IMBIPS[10] = "0,107,136,348,1684,1912,366,376,916,917,946,1577,3437,686,1920,1941,2661,2664,2694,1962";
                str_IMBIPS[11] = "0,107,348,414,1684,1912,896,916,917,925,960,1577,373,3437,686,1941,2661,2669,1938";
                str_IMBIPS[12] = "0,107,348,1684,1912,366,916,917,925,946,1577,3437,686,1941,2661,2669,1917,1943";
                str_IMBIPS[13] = "0,107,348,1684,1912,363,483,916,925,1577,1926,3437,686,2669,2742,1917,1946";
                str_IMBIPS[14] = "0,107,348,1684,1912,376,917,925,946,1926,3437,686,1941,2664,2679,1962";
                str_IMBIPS[15] = "0,107,348,1684,1912,363,896,925,946,1577,373,3437,686,2669,1918";
                str_IMBIPS[16] = "0,107,348,1684,1912,376,483,925,1577,3437,686,1941,2669,1917";
                str_IMBIPS[17] = "0,107,348,1684,1912,376,946,1577,3437,686,2669,1917,1929";
                str_IMBIPS[18] = "0,107,348,1684,1912,925,1577,3437,686,1941,2669,1962";
                str_IMBIPS[19] = "0,107,348,1684,1912,376,946,3437,686,1941,1943";
                str_IMBIPS[20] = "0,107,348,1684,1912,925,3437,686,2669,1938";
                str_IMBIPS[21] = "0,107,348,1684,1912,916,3437,1941,1938";
                str_IMBIPS[22] = "0,107,348,1684,1912,925,3437,1941";
                str_IMBIPS[23] = "107,348,1684,1912,916,3437,1918";
                str_IMBIPS[24] = "0,107,348,1684,1912,3437";
                str_IMBIPS[25] = "107,348,1684,1912,3437";
                str_IMBIPS[26] = "107,1684,1912,3437";
                str_IMBIPS[27] = "107,1684,1912";
                str_IMBIPS[28] = "107,1912";
                str_IMBIPS[29] = "107";

                str_CELF[0] = "107,1912,1684,3437,348,1941,946,0,1971,686,925,414,2669,1917,483,2661,916,1926,366,1014,2028,2754,1577,917,2778,953,376,1943,2742,3448";
                str_CELF[1] = "107,1912,1684,3437,348,1941,946,0,1971,686,925,414,2669,1917,483,2661,916,1926,366,1014,2028,2754,1577,917,2778,953,376,1943,2742";
                str_CELF[2] = "107,1912,1684,3437,348,1941,946,0,1971,686,925,414,2669,1917,483,2661,916,1926,366,1014,2028,2754,1577,917,2778,953,376,1943";
                str_CELF[3] = "107,1912,1684,3437,348,1941,946,0,1971,686,925,414,2669,1917,483,2661,916,1926,366,1014,2028,2754,1577,917,2778,953,376";
                str_CELF[4] = "107,1912,1684,3437,348,1941,946,0,1971,686,925,414,2669,1917,483,2661,916,1926,366,1014,2028,2754,1577,917,2778,953";
                str_CELF[5] = "107,1912,1684,3437,348,1941,946,0,1971,686,925,414,2669,1917,483,2661,916,1926,366,1014,2028,2754,1577,917,2778";
                str_CELF[6] = "107,1912,1684,3437,348,1941,946,0,1971,686,925,414,2669,1917,483,2661,916,1926,366,1014,2028,2754,1577,917";
                str_CELF[7] = "107,1912,1684,3437,348,1941,946,0,1971,686,925,414,2669,1917,483,2661,916,1926,366,1014,2028,2754,1577";
                str_CELF[8] = "107,1912,1684,3437,348,1941,946,0,1971,686,925,414,2669,1917,483,2661,916,1926,366,1014,2028,2754";
                str_CELF[9] = "107,1912,1684,3437,348,1941,946,0,1971,686,925,414,2669,1917,483,2661,916,1926,366,1014,2028";
                str_CELF[10] = "107,1912,1684,3437,348,1941,946,0,1971,686,925,414,2669,1917,483,2661,916,1926,366,1014";
                str_CELF[11] = "107,1912,1684,3437,348,1941,946,0,1971,686,925,414,2669,1917,483,2661,916,1926,366";
                str_CELF[12] = "107,1912,1684,3437,348,1941,946,0,1971,686,925,414,2669,1917,483,2661,916,1926";
                str_CELF[13] = "107,1912,1684,3437,348,1941,946,0,1971,686,925,414,2669,1917,483,2661,916";
                str_CELF[14] = "107,1912,1684,3437,348,1941,946,0,1971,686,925,414,2669,1917,483,2661";
                str_CELF[15] = "107,1912,1684,3437,348,1941,946,0,1971,686,925,414,2669,1917,483";
                str_CELF[16] = "107,1912,1684,3437,348,1941,946,0,1971,686,925,414,2669,1917";
                str_CELF[17] = "107,1912,1684,3437,348,1941,946,0,1971,686,925,414,2669";
                str_CELF[18] = "107,1912,1684,3437,348,1941,946,0,1971,686,925,414";
                str_CELF[19] = "107,1912,1684,3437,348,1941,946,0,1971,686,925";
                str_CELF[20] = "107,1912,1684,3437,348,1941,946,0,1971,686";
                str_CELF[21] = "107,1912,1684,3437,348,1941,946,0,1971";
                str_CELF[22] = "107,1912,1684,3437,348,1941,946,0";
                str_CELF[23] = "107,1912,1684,3437,348,1941,946";
                str_CELF[24] = "107,1912,1684,3437,348,1941";
                str_CELF[25] = "107,1912,1684,3437,348";
                str_CELF[26] = "107,1912,1684,3437";
                str_CELF[27] = "107,1912,1684";
                str_CELF[28] = "107,1912";
                str_CELF[29] = "107";




                str_IMM[0] = "107,1684,1912,3437,348,0,686,370,21,946,1918,2669,917,2661,414,916,3448,2724,3980,688,9,2665,698,1927,3442,1085,1926,353,3506,896";
                str_IMM[1] = "107,1684,1912,3437,348,0,686,21,370,2669,1917,917,946,2730,1085,694,3980,367,9,2661,1926,3442,3448,414,698,916,3506,1919,1918";
                str_IMM[2] = "107,1684,1912,3437,348,0,686,414,21,1917,917,946,2669,370,1085,2665,9,694,2661,916,3442,3448,1926,3980,366,698,2724,3506";
                str_IMM[3] = "107,1684,1912,3437,348,0,686,414,21,916,917,1917,2664,2661,3442,1085,694,370,946,2730,3980,26,3448,1926,698,3506,366";
                str_IMM[4] = "107,1684,1912,3437,348,0,686,414,21,946,917,2716,1917,2669,370,2730,3442,1926,694,9,1085,916,3980,2661,1927,363";
                str_IMM[5] = "107,1684,1912,3437,348,0,686,21,414,916,1917,917,2669,2661,3448,1926,376,3980,688,2730,946,9,3442,1085,366";
                str_IMM[6] = "107,1684,1912,3437,348,0,686,21,414,917,916,2669,1929,2661,370,694,2730,9,1085,1926,3442,3980,698,921";
                str_IMM[7] = "107,1684,1912,3437,348,0,686,414,21,916,1917,917,2664,694,376,2730,1085,3442,9,2661,3980,1926,698";
                str_IMM[8] = "107,1684,1912,3437,348,0,686,370,21,917,925,2669,1917,2661,3448,688,414,3442,26,946,3980,1964";
                str_IMM[9] = "107,1684,1912,3437,348,0,686,414,21,917,1917,946,2661,9,2679,1085,2730,370,694,3980,3442";
                str_IMM[10] = "107,1684,1912,3437,348,0,686,414,21,917,2669,1917,946,2661,370,3980,697,1085,9,2724";
                str_IMM[11] = "107,1684,1912,3437,348,0,686,414,21,917,946,1917,3448,2661,2664,694,370,2730,3442";
                str_IMM[12] = "107,1684,1912,3437,348,0,686,21,370,946,1917,917,3980,2730,414,2669,2661,694";
                str_IMM[13] = "107,1684,1912,3437,0,348,686,414,21,1917,946,2669,917,2661,376,2730,9";
                str_IMM[14] = "107,1684,1912,3437,0,348,686,414,21,946,1938,2669,917,3980,2661,1926";
                str_IMM[15] = "107,1684,1912,3437,0,348,686,414,21,946,1917,2669,917,3980,2661";
                str_IMM[16] = "107,1684,1912,3437,348,0,686,21,414,916,917,1938,2724,2664";
                str_IMM[17] = "107,1684,1912,3437,348,0,686,414,9,917,946,2669,1918";
                str_IMM[18] = "107,1684,1912,3437,348,0,686,370,21,916,2669,917";
                str_IMM[19] = "107,1684,1912,3437,0,348,686,414,21,946,917";
                str_IMM[20] = "107,1684,1912,3437,348,0,686,414,946,21";
                str_IMM[21] = "107,1684,1912,3437,348,0,686,414,21";
                str_IMM[22] = "107,1684,1912,3437,348,0,686,370";
                str_IMM[23] = "107,1684,1912,3437,348,0,686";
                str_IMM[24] = "107,1684,1912,3437,0,348";
                str_IMM[25] = "107,1684,1912,3437,348";
                str_IMM[26] = "107,1684,1912,3437";
                str_IMM[27] = "107,1684,1912";
                str_IMM[28] = "107,1684";
                str_IMM[29] = "107";
            }

            //string[] str_IMBIP = new string[4]; str_IMBIP[0] = strIMBIP5; str_IMBIP[1] = strIMBIP10; str_IMBIP[2] = strIMBIP20; str_IMBIP[3] = strIMBIP30;
            //string[] str_IMBIPS = new string[4]; str_IMBIPS[0] = strIMBIPS5; str_IMBIPS[1] = strIMBIPS10; str_IMBIPS[2] = strIMBIPS20; str_IMBIPS[3] = strIMBIPS30;
            //string[] str_CELF = new string[4]; str_CELF[0] = strCELF5; str_CELF[1] = strCELF10; str_CELF[2] = strCELF20; str_CELF[3] = strCELF30;
            //string[] str_IMM = new string[4]; str_IMM[0] = strIMM5; str_IMM[1] = strIMM10; str_IMM[2] = strIMM20; str_IMM[3] = strIMM30;

            str_IMBIP[0] = strIMBIPS10;
            str_IMBIPS[0] = strIMM10;

            //initialize_SAA_neighbourhood(SAA_M, SAA_N1);
            int repetition = 10;
            double[,] obj_IMBIP = new double[size, repetition];
            double[,] obj_IMBIPS = new double[size, repetition];
            double[,] obj_CELF = new double[size, repetition];
            double[,] obj_IMM = new double[size, repetition];
            StreamWriter swr = new StreamWriter("only" + filename + ".txt");

            List<List<int>> only_IMBIP = new List<List<int>>();
            List<List<int>> only_IMBIPS = new List<List<int>>();
            List<List<int>> only_CELF = new List<List<int>>();
            List<List<int>> only_IMM = new List<List<int>>();

            for (int index = 0; index < size; index++)
            {

                string[] lines_arr1 = str_IMBIP[index].Split(new char[] { ',' });
                string[] lines_arr2 = str_IMBIPS[index].Split(new char[] { ',' });
                //string[] lines_arr3 = str_CELF[index].Split(new char[] { ',' });
                //string[] lines_arr4 = str_IMM[index].Split(new char[] { ',' });

                //string[] lines = System.IO.File.ReadAllLines(@"D:\zz_doktora\ourpapers\2017\IMP-Linear\dataset\seeds.txt");
                //string[] lines = System.IO.File.ReadAllLines(@"D:\Influence-marketing\Code\influencer-1\weighted_imm_50.txt");
                List<int> temp1 = new List<int>();
                foreach (string str in lines_arr1)
                {
                    //temp1.Add(Convert.ToUInt16(str));
                    temp1.Add((int)node_set.IndexOf(int.Parse(str)));

                }
                only_IMBIP.Add(temp1);

                List<int> temp2 = new List<int>();
                foreach (string str in lines_arr2)
                {
                    //temp2.Add(Convert.ToUInt16(str));
                    temp2.Add((int)node_set.IndexOf(int.Parse(str)));
                }
                only_IMBIPS.Add(temp2);

                //List<int> temp3 = new List<int>();
                //foreach (string str in lines_arr3)
                //{
                //    //temp3.Add(Convert.ToUInt16(str));
                //    temp3.Add(node_set.IndexOf(Convert.ToUInt16(str)));
                //}
                //only_CELF.Add(temp3);

                //List<int> temp4 = new List<int>();
                //foreach (string str in lines_arr4)
                //{
                //    //temp4.Add(Convert.ToUInt16(str));
                //    temp4.Add(node_set.IndexOf(Convert.ToUInt16(str)));
                //}
                //only_IMM.Add(temp4);



                //determine_network_trees(SAA_N1);
                System.Console.WriteLine("Iter-" + index);
                for (int rep = 0; rep < repetition; rep++)
                {
                    initialize_SAA_3_prb_list();
                    System.Console.WriteLine("Rep-" + rep);
                    obj_IMBIP[index, rep] = evaluate_influence(only_IMBIP[index], SAA_M, SAA_N2, 5);
                    obj_IMBIPS[index, rep] = evaluate_influence(only_IMBIPS[index], SAA_M, SAA_N2, 5);
                    //obj_CELF[index, rep] = evaluate_influence(only_CELF[index], SAA_M, SAA_N2, 5);
                    //obj_IMM[index, rep] = evaluate_influence(only_IMM[index], SAA_M, SAA_N2, 5);
                    //System.Console.WriteLine(index + "; " + obj_IMBIP[index, rep] + ";" + obj_IMBIPS[index, rep] + ";" + obj_CELF[index, rep] + ";" + obj_IMM[index, rep] + ";");
                    System.Console.WriteLine(index + "; " + obj_IMBIP[index, rep] + ";" + obj_IMBIPS[index, rep]);
                    //swr.WriteLine(index + "; " + obj_IMBIP[index, rep] + ";" + obj_IMBIPS[index, rep] + ";" + obj_CELF[index, rep] + ";" + obj_IMM[index, rep] + ";");
                }

            }
            swr.Close();

        }


        #region statistics

        // The random generator seed can be set three ways:
        // 1) specifying two non-zero unsigned integers
        // 2) specifying one non-zero unsigned integer and taking a default value for the second
        // 3) setting the seed from the system time

        public static void SetSeed(uint u, uint v)
        {

            if (u != 0) m_w = u;
            if (v != 0) m_z = v;
        }

        public static void SetSeed(uint u)
        {
            m_w = u;
        }

        public static void SetSeedFromSystemTime()
        {
            System.DateTime dt = System.DateTime.Now;
            long x = dt.ToFileTime();
            SetSeed((uint)(x >> 16), (uint)(x % 4294967296));
        }

        // Produce a uniform random sample from the open interval (0, 1).
        // The method will not return either end point.
        public static double GetUniform()
        {
            // 0 <= u < 2^32
            uint u = GetUint();
            // The magic number below is 1/(2^32 + 2).
            // The result is strictly between 0 and 1.
            return (u + 1.0) * 2.328306435454494e-10;
        }

        // This is the heart of the generator.
        // It uses George Marsaglia's MWC algorithm to produce an unsigned integer.
        // See http://www.bobwheeler.com/statistics/Password/MarsagliaPost.txt
        private static uint GetUint()
        {
            m_z = 36969 * (m_z & 65535) + (m_z >> 16);
            m_w = 18000 * (m_w & 65535) + (m_w >> 16);
            return (m_z << 16) + m_w;
        }

        // Get normal (Gaussian) random sample with mean 0 and standard deviation 1
        public static double GetNormal()
        {
            // Use Box-Muller algorithm
            double u1 = GetUniform();
            double u2 = GetUniform();
            double r = Math.Sqrt(-2.0 * Math.Log(u1));
            double theta = 2.0 * Math.PI * u2;
            return r * Math.Sin(theta);
        }

        // Get normal (Gaussian) random sample with specified mean and standard deviation
        public static double GetNormal(double mean, double standardDeviation)
        {
            if (standardDeviation <= 0.0)
            {
                string msg = string.Format("Shape must be positive. Received {0}.", standardDeviation);
                throw new ArgumentOutOfRangeException(msg);
            }
            return mean + standardDeviation * GetNormal();
        }

        // Get exponential random sample with mean 1
        public static double GetExponential()
        {
            return -Math.Log(GetUniform());
        }

        // Get exponential random sample with specified mean
        public static double GetExponential(double mean)
        {
            if (mean <= 0.0)
            {
                string msg = string.Format("Mean must be positive. Received {0}.", mean);
                throw new ArgumentOutOfRangeException(msg);
            }
            return mean * GetExponential();
        }

        public static double GetGamma(double shape, double scale)
        {
            // Implementation based on "A Simple Method for Generating Gamma Variables"
            // by George Marsaglia and Wai Wan Tsang.  ACM Transactions on Mathematical Software
            // Vol 26, No 3, September 2000, pages 363-372.

            double d, c, x, xsquared, v, u;

            if (shape >= 1.0)
            {
                d = shape - 1.0 / 3.0;
                c = 1.0 / Math.Sqrt(9.0 * d);
                for (; ; )
                {
                    do
                    {
                        x = GetNormal();
                        v = 1.0 + c * x;
                    }
                    while (v <= 0.0);
                    v = v * v * v;
                    u = GetUniform();
                    xsquared = x * x;
                    if (u < 1.0 - .0331 * xsquared * xsquared || Math.Log(u) < 0.5 * xsquared + d * (1.0 - v + Math.Log(v)))
                        return scale * d * v;
                }
            }
            else if (shape <= 0.0)
            {
                string msg = string.Format("Shape must be positive. Received {0}.", shape);
                throw new ArgumentOutOfRangeException(msg);
            }
            else
            {
                double g = GetGamma(shape + 1.0, 1.0);
                double w = GetUniform();
                return scale * g * Math.Pow(w, 1.0 / shape);
            }
        }

        public static double GetChiSquare(double degreesOfFreedom)
        {
            // A chi squared distribution with n degrees of freedom
            // is a gamma distribution with shape n/2 and scale 2.
            return GetGamma(0.5 * degreesOfFreedom, 2.0);
        }

        public static double GetInverseGamma(double shape, double scale)
        {
            // If X is gamma(shape, scale) then
            // 1/Y is inverse gamma(shape, 1/scale)
            return 1.0 / GetGamma(shape, 1.0 / scale);
        }

        public static double GetWeibull(double shape, double scale)
        {
            if (shape <= 0.0 || scale <= 0.0)
            {
                string msg = string.Format("Shape and scale parameters must be positive. Recieved shape {0} and scale{1}.", shape, scale);
                throw new ArgumentOutOfRangeException(msg);
            }
            return scale * Math.Pow(-Math.Log(GetUniform()), 1.0 / shape);
        }

        public static double GetCauchy(double median, double scale)
        {
            if (scale <= 0)
            {
                string msg = string.Format("Scale must be positive. Received {0}.", scale);
                throw new ArgumentException(msg);
            }

            double p = GetUniform();

            // Apply inverse of the Cauchy distribution function to a uniform
            return median + scale * Math.Tan(Math.PI * (p - 0.5));
        }

        public static double GetStudentT(double degreesOfFreedom)
        {
            if (degreesOfFreedom <= 0)
            {
                string msg = string.Format("Degrees of freedom must be positive. Received {0}.", degreesOfFreedom);
                throw new ArgumentException(msg);
            }

            // See Seminumerical Algorithms by Knuth
            double y1 = GetNormal();
            double y2 = GetChiSquare(degreesOfFreedom);
            return y1 / Math.Sqrt(y2 / degreesOfFreedom);
        }

        // The Laplace distribution is also known as the double exponential distribution.
        public static double GetLaplace(double mean, double scale)
        {
            double u = GetUniform();
            return (u < 0.5) ?
                mean + scale * Math.Log(2.0 * u) :
                mean - scale * Math.Log(2 * (1 - u));
        }

        public static double GetLogNormal(double mu, double sigma)
        {
            return Math.Exp(GetNormal(mu, sigma));
        }

        public static double GetBeta(double a, double b)
        {
            if (a <= 0.0 || b <= 0.0)
            {
                string msg = string.Format("Beta parameters must be positive. Received {0} and {1}.", a, b);
                throw new ArgumentOutOfRangeException(msg);
            }

            // There are more efficient methods for generating beta samples.
            // However such methods are a little more efficient and much more complicated.
            // For an explanation of why the following method works, see
            // http://www.johndcook.com/distribution_chart.html#gamma_beta

            double u = GetGamma(a, 1.0);
            double v = GetGamma(b, 1.0);
            return u / (u + v);
        }
        #endregion

        public static void parallel_example()
        {
            int[] input = { 4, 4, 6, 2, 9, 5, 10, 3 };
            int sum = 0;


            Parallel.ForEach(
                    input,                          // source collection
                    () => 0,                            // thread local initializer
                    (n, loopState, localSum) =>     // body
                    {
                        localSum += n;
                        Console.WriteLine("Thread={0}, n={1}, localSum={2}", Thread.CurrentThread.ManagedThreadId, n, localSum);
                        return localSum;
                    },
                    (localSum) => System.Threading.Interlocked.Add(ref sum, localSum)                    // thread local aggregator
                );

            Console.WriteLine("\nSum={0}", sum);
        }
    }
}