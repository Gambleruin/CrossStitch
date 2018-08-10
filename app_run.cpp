#include "crosstitch.cpp"

vector<string> readFileToVector(const string& filename)
{
    ifstream source;
    source.open(filename);
    vector<string> lines;
    string line;
    while (getline(source, line))
    {
        lines.push_back(line);
    }
    return lines;
}

int main(int argc, char* argv[]){

	//handling the input
    if(argc != 2){
        cerr << "Usage: "<< argv[0]
            << "input.txt" <<endl;
        return 1;
    }

    string f(argv[1]);
    vector<string> pattern = readFileToVector(f);
    
    //running the algorithm 
    CrossStitch crosstitch;
    cout <<crosstitch.embroider(pattern)<<"\n";



    return 0;
}
