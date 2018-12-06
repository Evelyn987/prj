

#include <iostream>
#include <sstream>
#include <utility>
#include <climits>
#include <algorithm>
#include <map>
#include <string>
#include <vector>
#include <atomic>
#include <thread>
#include <pthread.h>
#include <semaphore.h>

#include <array>
// defined std::unique_ptr
#include <memory>
// defines Var and Lit
#include "minisat/core/SolverTypes.h"
// defines Solver
#include "minisat/core/Solver.h"


// Saved all the edges added
std::vector<std::pair<int, int> > edges;

// Saved all the nodes with its' number in list
std::map<int, std::vector<int> > allTable;

struct threadcontent {
pthread_t threadtry;
int nums;
};

sem_t input_semaphore;
sem_t output_semaphore;
sem_t trueout_semaphore;
pthread_mutex_t save_mutex;
int vertexnumber = -1;


// Push different methods' vertex cover into a table
// and wait for output
void OutputTable(std::vector<int> table, int name) {
    pthread_mutex_lock(&save_mutex);
    allTable.insert( std::pair<int, std::vector<int> >(name, table));
    pthread_mutex_unlock(&save_mutex);
}

// Print three methods in order
void ThreadTable() {
    sem_wait(&trueout_semaphore);
    if (allTable.size() == 3) {
        std::vector<int> table1 = allTable[1];
        std::vector<int> table2 = allTable[2];
        std::vector<int> table3 = allTable[3];
        std::cout << "CNF-SAT-VC: ";
        for (auto i = table1.begin(); i != table1.end(); ++i) {
            if ( i == table1.end() - 1) {
                std::cout << *i;
            } else {
                std::cout << *i << ',';
            }
        }
        std::cout << std::endl;
        std::cout << "APPROX-VC-1: ";
        for (auto i = table2.begin(); i != table2.end(); ++i) {
            if ( i == table2.end() - 1) {
                std::cout << *i;
            } else {
                std::cout << *i << ',';
            }
        }
        std::cout << std::endl;
        std::cout << "APPROX-VC-2: ";
        for (auto i = table3.begin(); i != table3.end(); ++i) {
            if ( i == table3.end() - 1) {
                std::cout << *i;
            } else {
                std::cout << *i << ',';
            }
        }
        std::cout << std::endl;
    } else {
        std::cout << "CNF-SAT-VC: \n";
        std::cout << "APPROX-VC-1: \n";
        std::cout << "APPROX-VC-2: \n";
    }
}

// Calculate if the given number of vertex is enough for Vertex cover
bool CheckPossible(int vertexnum, int covernum) {
    std::unique_ptr<Minisat::Solver> solver(new Minisat::Solver());
    Minisat::Lit listofliteral[covernum][vertexnum];
    for (int i = 0; i < covernum; i++) {
        for (int j = 0; j < vertexnum; j++) {
            listofliteral[i][j] = Minisat::mkLit(solver->newVar());
        }
    }
    Minisat::vec<Minisat::Lit> litonevertex;
    for (int i = 0; i < covernum; i++) {
        for (int j = 0; j < vertexnum; j++) {
            litonevertex.push(listofliteral[i][j]);
        }
        solver ->addClause(litonevertex);
    }
    for (int j = 0; j < vertexnum; j++) {
        for (int i = 0; i < covernum; i++) {
            for (int k = i + 1; k < covernum; k++) {
                solver -> addClause(~listofliteral[i][j], ~listofliteral[k][j]);
            }
        }
    }
    for (int i = 0; i < covernum; i++) {
        for (int j = 0; j < vertexnum; j++) {
            for (int k = j + 1; k < vertexnum; k++) {
                solver -> addClause(~listofliteral[i][j], ~listofliteral[i][k]);
            }
        }
    }

    for ( std::pair<int, int> x : edges ) {
        int vertex1 = x.first;
        int vertex2 = x.second;
        Minisat::vec<Minisat::Lit> litverconnect;
        for (int i = 0; i < covernum; i++) {
            litverconnect.push(listofliteral[i][vertex1]);
            litverconnect.push(listofliteral[i][vertex2]);
        }
        solver -> addClause(litverconnect);
    }

    bool result = solver->solve();
    solver.reset (new Minisat::Solver());
    return result;
}

void GetTruthTable(int vertexnum, int covernum) {
    // -- allocate on the heap so that we can reset later if needed
    std::unique_ptr<Minisat::Solver> solver(new Minisat::Solver());
    Minisat::Lit listofliteral[covernum][vertexnum];
    for (int i = 0; i < covernum; i++) {
        for (int j = 0; j < vertexnum; j++) {
            listofliteral[i][j] = Minisat::mkLit(solver->newVar());
        }
    }
    Minisat::vec<Minisat::Lit> litonevertex;
    for (int i = 0; i < covernum; i++) {
        for (int j = 0; j < vertexnum; j++) {
            litonevertex.push(listofliteral[i][j]);
        }
        solver ->addClause(litonevertex);
    }
    for (int j = 0; j < vertexnum; j++) {
        for (int i =0; i < covernum; i++) {
            for (int k=i + 1; k < covernum; k++) {
                solver -> addClause(~listofliteral[i][j], ~listofliteral[k][j]);
            }
        }
    }
    for (int i = 0; i < covernum; i++) {
        for (int j = 0; j < vertexnum; j++) {
            for (int k=j + 1; k< vertexnum; k++) {
                solver -> addClause(~listofliteral[i][j], ~listofliteral[i][k]);
            }
        }
    }
    for ( std::pair<int, int> x : edges ) {
        int vertex1 = x.first;
        int vertex2 = x.second;

        Minisat::vec<Minisat::Lit> litverconnect;
        for (int i = 0; i < covernum; i++) {
            litverconnect.push(listofliteral[i][vertex1]);
            litverconnect.push(listofliteral[i][vertex2]);
        }
        solver -> addClause(litverconnect);
    }
    solver -> solve();
    std::vector<int> truthtalbe;

    for (int i = 0; i < covernum; i++) {
        for (int j = 0; j < vertexnum; j++) {
            if (Minisat::toInt(solver->modelValue(listofliteral[i][j])) == 0) {
                truthtalbe.push_back(j);
            }
        }
    }

    std::sort(truthtalbe.begin(), truthtalbe.end());
    sem_wait(&output_semaphore);
    OutputTable(truthtalbe, 1);
    sem_post(&output_semaphore);
}

void FindVertexCover(int vnum) {
    int vertexnum = vnum;
    int max = vertexnum;
    int min = 1;
    std::vector<int> possiblecover;
    while (true) {
        int covernum = min + (max - min) / 2;
        if (CheckPossible(vertexnum, covernum)) {
            possiblecover.push_back(covernum);
            max = covernum - 1;
        } else {
            min = covernum + 1;
        }
        if (max < min) {
            break;
        }
    }
    int mincover = vertexnum;
    for (int i : possiblecover) {
        if (i < vertexnum) {
            mincover = i;
        }
    }
    GetTruthTable(vertexnum, mincover);
}

// Print different errors to stdout
void ErrorPrinter(char type) {
    switch (type) {
        case 'i' :  std::cerr << "Error: Invalid Line\n";
                    edges.clear();
                    break;
        case 'l' :  std::cerr << "Error: Invalid Line\n";
                    break;
        case 'c' :  std::cerr << "Error: Invalid Command\n";
                    break;
        case 'n' :  std::cerr << "Error: Invalid Vertex in Edges\n";
                    break;
        case 'v' :  std::cerr << "Error: Vertex already existed\n";
                    break;
        case 'e' :  std::cerr << "Error: Edges already existed\n";
                    break;
        case 'p' :  std::cerr << "Error: There's no path \n";
                    break;
        default  :  std::cerr << "Error: Special error detected\n";
                    break;
    }
}

// Check if the vertex's label number is larger than number of Vertexs
//
// Return true when the label number is larger than limit
// Otherwise return false
bool CheckNumber(int limit, int label, bool inputfail) {
    if (inputfail) {
        ErrorPrinter('n');
        edges.clear();
        return true;
    }
    if (label > (limit - 1) || limit == 0) {
        ErrorPrinter('n');
        edges.clear();
        return true;
    }
    return false;
}

// Check if the input is valid
//
// Return true when the input symbol is valid
// Otherwise return false
bool CheckSymbol(char type, char symbol, bool inputfail) {
    if (inputfail) {
        ErrorPrinter('i');
        return true;
    }
    if (type != symbol) {
        ErrorPrinter('i');
        return true;
    }
    return false;
}

void * GraphOut(void * value) {
    threadcontent *second = static_cast<threadcontent*>(value);

    int vnum = second->nums;
    bool pass = false;
    if (!edges.empty()) {
        int count = 0;
        for ( std::pair<int, int> x : edges ) {
            if (x.first > (vnum - 1) || x.second > (vnum - 1)) {
                pass = true;
                break;
            } else if (x.first == x.second) {
                edges.erase(edges.begin() + count);
            }
            count++;
        }
        if (pass) {
            std::cerr << "Error: There's a vertex not existed\n";
        } else if (edges.empty()) {
            std::cout << std::endl;
        } else {
            FindVertexCover(vnum);
        }
    } else {
        std::cout << std::endl;
    }

    return NULL;
}

void PushEdge(int num1, int num2) {
    edges.push_back(std::make_pair(num1, num2));
}


void * call_from_thread3(void *arg) {

    std::vector<std::pair<int, int> > shareedge = edges;
    std::vector<int> truthtable;
    bool firsttime = true;
    int count = shareedge.size();
    count = random()% count;
    for ( std::vector<std::pair<int, int> >::iterator it = shareedge.begin(); it != shareedge.end(); ++it ) {
        if (firsttime) {
            truthtable.push_back((it + count)->first);
            truthtable.push_back((it + count)->second);
            firsttime = false;
        }
        if (std::find(truthtable.begin(), truthtable.end(), it->first) != truthtable.end() ||
        std::find(truthtable.begin(), truthtable.end(), it->second) != truthtable.end()) {

            shareedge.erase(it--);
        } else {
            truthtable.push_back(it->first);
            truthtable.push_back(it->second);
        }
    }
    std::sort(truthtable.begin(), truthtable.end());
    sem_wait(&output_semaphore);
    OutputTable(truthtable, 3);
    sem_post(&output_semaphore);

    return NULL;
}


void * call_from_thread(void* value) {
    threadcontent *third = static_cast<threadcontent*>(value);

    int vnum = third->nums;
    std::vector<std::pair<int, int> > shareedge = edges;
    std::vector<int> truthtable;
    std::map<int,int> countvertex;

    while (!shareedge.empty()) {
        countvertex.clear();
        for (int i = 0; i < vnum; i++) {
            countvertex.insert(std::pair<int, int>( i, 0));
        }
        for (int x : truthtable) {
            countvertex.erase(x);
        }
        for ( std::vector<std::pair<int, int> >::iterator it = shareedge.begin(); it != shareedge.end(); ++it ) {
            countvertex[it->first]++;
            countvertex[it->second]++;
        }
        bool firsttime = true;
        int maxvalue = 0;
        int indexformax = 0;
            for (std::pair<int, int> x: countvertex) {
            if (firsttime) {
                maxvalue = x.second;
                indexformax = x.first;
                firsttime = false;
            } else if (maxvalue < x.second) {
                maxvalue = x.second;
                indexformax = x.first;
            }
        }
        truthtable.push_back(indexformax);
        for ( std::vector<std::pair<int, int> >::iterator it = shareedge.begin(); it != shareedge.end(); ++it ) {
            if (it->first == indexformax || it->second == indexformax) {
                shareedge.erase(it--);
            }
        }
    }
    std::sort(truthtable.begin(), truthtable.end());
    sem_wait(&output_semaphore);
    OutputTable(truthtable, 2);
    sem_post(&output_semaphore);

    return NULL;
}


int readGraph() {
    char vore = ' ', symboll = ' ', bracl = ' ';
    char sept = ' ', bracr = ' ';
    int vnum = 0, num1 = 0, num2 = 0;
    bool verge_existed = false, edge_existed = false, first_verge = true;
    while (!std::cin.eof()) {
        std::string line;
        std::getline(std::cin, line);
        if ( std::cin.eof() ) {
            break;
        }
        std::istringstream input(line);
        while (!input.eof()) {
            input >> vore;
            if (first_verge) {
                if (vore != 'V') {
                    ErrorPrinter('c');
                    break;
                }
            }
            switch (vore) {
                case 'V' :  {   if (verge_existed) {
                                    ErrorPrinter('v');
                                    break;
                                }
                                if (input.fail() || vore != 'V') {
                                    ErrorPrinter('c');
                                    break;
                                }

                                input >> vnum;
                                if (input.fail()) {
                                    ErrorPrinter('l');
                                    break;
                                }
                                first_verge = false;
                                verge_existed = true;
                                edges.clear();
                                edge_existed = false;
                                continue;
                            }

            case 'E' :  {   if (edge_existed) {
                                ErrorPrinter('e');
                                break;
                              }
                            if (input.fail() || vore != 'E') {
                                ErrorPrinter('c');
                                break;
                            }
                            input >> symboll;
                            if (input.fail() || symboll != '{') {
                                ErrorPrinter('i');
                                break;
                            }
                            bool comma_existed = false;
                            while (!input.eof()) {
                                input >> bracl;
                                if (bracl == '}') {
                                    if (comma_existed) {
                                        ErrorPrinter('i');
                                        break;
                                    }
                                    edge_existed = true;
                                    verge_existed = false;
                                    vertexnumber = vnum;
                                    sem_post(&input_semaphore);
                                    ThreadTable();
                                    return 0;
                                    break;
                                }
                                if (CheckSymbol('<', bracl, input.fail())) {
                                    break;
                                }
                                input >> num1;
                                if (CheckNumber(vnum, num1, input.fail())) {
                                    edges.clear();
                                    break;
                                }
                                input >> sept;
                                if (CheckSymbol(',', sept, input.fail())) {
                                    break;
                                }
                                input >> num2;
                                if (CheckNumber(vnum, num2, input.fail())) {
                                    break;
                                }
                                input >> bracr;
                                if (CheckSymbol('>', bracr, input.fail())) {
                                    break;
                                }
                                edges.push_back(std::make_pair(num1, num2));
                                input >> sept;
                                if (input.fail()) {
                                    ErrorPrinter('i');
                                    break;
                                } else if (sept == '}') {
                                    edge_existed = true;
                                    verge_existed = false;
                                    vertexnumber = vnum;
                                    sem_post(&input_semaphore);
                                    ThreadTable();
                                    return 0;

                                    break;
                                }
                                if (CheckSymbol(',', sept, input.fail())) {
                                    break;
                                }
                                comma_existed = true;
                            }
                        break;
                        }
            default :   ErrorPrinter('c');
                        break;
            }
            break;
        }
    }
    sem_post(&input_semaphore);
    return -1;
}


int main(int argc, char** argv) {

    while (!std::cin.eof()) {
        threadcontent *second = new threadcontent();
        threadcontent *third = new threadcontent();
        threadcontent *fourth = new threadcontent();
        sem_init(&trueout_semaphore, 0, 0);
        sem_init(&output_semaphore, 0 ,1);
        sem_init(&input_semaphore, 0, 0);

        std::atomic<int> vnum {0};
        std::thread first(readGraph);

        sem_wait(&input_semaphore);
        int num = vertexnumber;
        if (num == -1) {
            first.join();
            delete second;
            delete third;
            delete fourth;
            break;
        } else if (edges.size() == 0) {
            sem_post(&trueout_semaphore);
            first.join();
            delete second;
            delete third;
            delete fourth;
            continue;
        }

        second->nums = num;
        third->nums = num;
        pthread_create(&(second->threadtry), NULL, GraphOut, (void *)second);
        pthread_create(&(third->threadtry), NULL, call_from_thread, (void *)third);
        pthread_create(&(fourth->threadtry), NULL, call_from_thread3, (void *)fourth);


        pthread_join(second->threadtry, NULL);
        pthread_join(third->threadtry, NULL);
        pthread_join(fourth->threadtry, NULL);


        sem_post(&trueout_semaphore);
        first.join();

        delete second;
        delete third;
        delete fourth;

        allTable.clear();
        edges.clear();
        vertexnumber = -1;
    }

}
