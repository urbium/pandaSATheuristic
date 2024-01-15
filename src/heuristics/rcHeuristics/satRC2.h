#include "../Heuristic.h"
#include "../../Model.h"
#include <cstdio>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <array>
#include <fstream>
#include <sstream>
#include <cmath>
#include "../ProgressionNetwork.h"
#include <stdexcept>

class satRC2 : public Heuristic
{
private:
    int actionCost;
    int hardClauseCost;
    vector<int> varActionToRealAction;
    vector<int> firstActionOfEachStep;
    vector<vector<int>> precsIntermediate;
    vector<vector<int>> delsIntermediate;
    Model *htn;

    int exec(const char *cmd)
    { // taken from stackoverflow and adapted
        std::array<char, 128> buffer;
        long int res = -1;
        std::unique_ptr<FILE, decltype(&pclose)> pipe(popen((std::string(cmd) + " 2>/dev/null").c_str(), "r"), pclose);
        if (!pipe)
        {
            throw std::runtime_error("popen() failed!");
        }
        while (fgets(buffer.data(), buffer.size(), pipe.get()) != nullptr)
        {
            // cout << buffer.data() << endl;
            if (buffer[0] == 's')
            {
                if (strcmp(buffer.data() + 2, "UNSATISFIABLE\n") == 0)
                {
                    return -1;
                }
            }
            else if (buffer[0] == 'o')
            {
                try
                {
                    res = round(stol((buffer.data() + 2)));
                }
                catch (const out_of_range &e)
                {
                    res = numeric_limits<int>::max();
                }
            }
        }
        return res;
    }

    void adapt(int numVars, int numClauses, int maxCost, const std::string &filename)
    {
        std::fstream file(filename, std::ios::in | std::ios::out);

        file.seekp(0);
        file.write(pad_string_to_32_bytes("p wcnf " + to_string(numVars) + " " + to_string(numClauses) + " " + to_string(maxCost)).c_str(), 32);

        file.close();
    }

    string pad_string_to_32_bytes(const std::string &input) // taken from chatgpt
    {
        std::ostringstream oss;
        oss << input;
        int num_spaces = 32 - input.length() - 1; // Subtract 1 for the newline character
        for (int i = 0; i < num_spaces; ++i)
        {
            oss << " ";
        }
        oss << '\n';
        return oss.str();
    }

    void addHardClause(std::ofstream &file, int variable)
    {
        file << hardClauseCost << " " << variable << " 0" << endl;
    }

    void addHardClauseNeg(std::ofstream &file, int variable)
    {
        file << hardClauseCost << " -" << variable << " 0" << endl;
    }

    void addHardClauseFirstNegSecTrue(std::ofstream &file, int negClause, int posClause)
    {
        file << hardClauseCost << " -" << negClause << " " << posClause << " 0" << endl;
    }

    void addHardClauseTwoNegOneTrue(std::ofstream &file, int negClause1, int negClause2, int posClause)
    {
        file << hardClauseCost << " -" << negClause1 << " -" << negClause2 << " " << posClause << " 0" << endl;
    }

    void addHardClauseTwoNegTwoTrue(std::ofstream &file, int negClause1, int negClause2, int posClause1, int posClause2)
    {
        file << hardClauseCost << " -" << negClause1 << " -" << negClause2 << " " << posClause1 << " " << posClause2 << " 0" << endl;
    }

    void addNegatedAction(std::ofstream &file, int action)
    {
        file << actionCost << " -" << action << " 0" << endl;
    }

    void addNegatedOrdering(std::ofstream &file, int oC)
    {
        file << "1 -" << oC << " 0" << endl;
    }

    void addHardClauseFirstNegVectorTrue(std::ofstream &file, int negClause, vector<int> posClauses)
    {
        file << hardClauseCost << " -" << negClause;
        for (int pC : posClauses)
        {
            file << " " << pC;
        }
        file << " 0" << endl;
    }

    

    int getNumActions(searchNode *n)
    {
        int stepsPrint = 0;
        planStep *temp;

        if (n->numAbstract > 0)
        {
            temp = n->unconstraintAbstract[0];
        }
        else if (n->numPrimitive > 0)
        {
            temp = n->unconstraintPrimitive[0];
        }
        else
        {
            return -1;
        }

        stepsPrint++;

        firstActionOfEachStep.push_back(1);
        int result = 1;                      // Initial Action
        varActionToRealAction.push_back(-1); // added one in addition so that the numbers of the vars actually match
        varActionToRealAction.push_back(-1); // Position 1 is start action

        firstActionOfEachStep.push_back(result + 1);
        vector<int> helperDels;
        if (temp->task < htn->numActions)
        {
            for (int i = 0; i < htn->numDels[temp->task]; i++)
            {
                helperDels.push_back(htn->delLists[temp->task][i]);
            }
        }
        else
        {
            for (int del : htn->eff_negative[temp->task - htn->numActions])
            {
                helperDels.push_back(del);
            }
        }

        delsIntermediate.push_back(helperDels);

        // cout << temp->task << endl;

        for (int j = 0; j < htn->numReachable[temp->task]; j++)
        {
            if (htn->reachable[temp->task][j] < htn->numActions)
            {
                result++;
                varActionToRealAction.push_back(htn->reachable[temp->task][j]);
            }
        }
        while (temp->numSuccessors > 0)
        {
            stepsPrint++;
            temp = temp->successorList[0];
            // cout << temp->task - htn->numActions<< endl;
            firstActionOfEachStep.push_back(result + 1);
            if (temp->task < htn->numActions)
            {
                result++;
                varActionToRealAction.push_back(temp->task);
                vector<int> helperPrecs;
                for (int i = 0; i < htn->numPrecs[temp->task]; i++)
                {
                    helperPrecs.push_back(htn->precLists[temp->task][i]);
                }
                vector<int> helperDels;
                for (int i = 0; i < htn->numDels[temp->task]; i++)
                {
                    helperDels.push_back(htn->delLists[temp->task][i]);
                }
                delsIntermediate.push_back(helperDels);
                precsIntermediate.push_back(helperPrecs);
            }
            else
            {
                for (int j = 0; j < htn->numReachable[temp->task]; j++)
                {
                    if (htn->reachable[temp->task][j] < htn->numActions)
                    {
                        result++;
                        varActionToRealAction.push_back(htn->reachable[temp->task][j]);
                    }
                }
                vector<int> helperPrecs;
                for (int prec : htn->preconditions[temp->task - htn->numActions])
                {
                    helperPrecs.push_back(prec);
                }
                vector<int> helperDels;
                for (int del : htn->eff_negative[temp->task - htn->numActions])
                {
                    helperDels.push_back(del);
                }
                delsIntermediate.push_back(helperDels);
                precsIntermediate.push_back(helperPrecs);
            }

            // for (int j = 0; j < htn->numReachable[temp->task]; j++) {
            //     if (htn->reachable[temp->task][j] < htn->numActions){
            //         result++;
            //         varActionToRealAction.push_back(htn->reachable[temp->task][j]);
            //     }
            // }
            // if (temp->task<htn->numActions){
            //     vector<int> helperPrecs;
            //     for (int i = 0; i < htn->numPrecs[temp->task]; i++){
            //         helperPrecs.push_back(htn->precLists[temp->task][i]);
            //     }
            //     precsIntermediate.push_back(helperPrecs);
            // } else {
            //     vector<int> helperPrecs;
            //     for (int prec : htn->preconditions[temp->task-htn->numActions]){
            //         helperPrecs.push_back(prec);
            //     }
            //     precsIntermediate.push_back(helperPrecs);
            // }
        }
        varActionToRealAction.push_back(-1); // goal action
        result++;
        firstActionOfEachStep.push_back(result);

        delsIntermediate.pop_back();

        cout << "Num Steps: " << stepsPrint << endl;

        return result;
    }

    int addInDelInt(int bPI, int add)
    {
        // We are in an action >= firstActionOfEachStep[breakPointIndex]
        // Return the index of the last intermediate Task delting the add Effect before the given (through bpi)
        // Returns -1 if add does not get deleted up to that bpi
        if (bPI == 1)
        {
            return -1;
        }
        for (int i = bPI - 2; i >= 0; i--)
        {
            for (int delIndex = 0; delIndex < delsIntermediate[i].size(); delIndex++)
            {
                if (add == delsIntermediate[i][delIndex])
                {
                    return i;
                }
            }
        }
        return -1;
    }

    void makeFile(const std::string &filename, searchNode *n)
    {
        int numActions = getNumActions(n);

        if (numActions == -1)
        {
            ofstream file(filename);
            if (!file)
            {
                cerr << "Error: Could not open file." << std::endl;
                return;
            }
            file << "p wcnf 2 1" << endl;
            file << "2 1 2 0" << endl;
            file.close();
            return;
        }

        int goalAction = numActions;
        int numSteps = firstActionOfEachStep.size();
        numActions = numActions + numSteps - 3; // intermediate actions between steps without one for the goal and inital action

        cout << "Num Actions: " << numActions << endl;

        actionCost = numActions*numActions+1;
        hardClauseCost = (numActions+1) * actionCost + 1;
        unsigned long long int numClauses = 0;
        int **orderingArray = new int *[numActions + 1];
        int orderingCounter = 1;

        for (int a1 = 1; a1 <= numActions; a1++)
        {
            orderingArray[a1] = new int[numActions + 1];
            for (int a2 = 1; a2 <= numActions; a2++)
            {
                orderingArray[a1][a2] = numActions + orderingCounter;
                orderingCounter++;
            }
        }

        ofstream file(filename);
        if (!file)
        {
            cerr << "Error: Could not open file." << std::endl;
            return;
        }

        file << pad_string_to_32_bytes("Hello There");

        file << "c Paper 2" << endl;
        // Paper (2)
        addHardClause(file, 1);
        addHardClause(file, goalAction);
        numClauses = numClauses + 2;

        // //add all intermediate actions as hard-clauses
        // for (int a = goalAction+1; a <= numActions; a++){
        //     addHardClause(file, a);
        //     numClauses++;
        // }

        file << "c Paper 1+3" << endl;
        // Paper (1) + (3)
        for (int a1 = 1; a1 <= numActions; a1++)
        {
            for (int a2 = 1; a2 <= numActions; a2++)
            {
                if (a2 == a1)
                {
                    addHardClauseNeg(file, orderingArray[a1][a2]); // Paper (1)
                    numClauses++;
                    continue;
                }
                addHardClauseFirstNegSecTrue(file, orderingArray[a1][a2], a1); // Paper (3)
                addHardClauseFirstNegSecTrue(file, orderingArray[a1][a2], a2); // Paper (3)
                addNegatedOrdering(file, orderingArray[a1][a2]);
                addNegatedOrdering(file, orderingArray[a2][a1]);
                numClauses = numClauses + 4;
            }
        }

        file << "c Paper 4" << endl;
        // Paper (4)
        for (int a = 2; a <= numActions; a++)
        {
            if (a == goalAction)
            {
                continue;
            }
            addHardClauseFirstNegSecTrue(file, a, orderingArray[1][a]);
            addHardClauseFirstNegSecTrue(file, a, orderingArray[a][goalAction]);
            numClauses = numClauses + 2;
        }

        timeval tp;
        gettimeofday(&tp, NULL);
        long startT = tp.tv_sec * 1000 + tp.tv_usec / 1000;

        int s5Clauses = numClauses;
        file << "c Paper 5" << endl;
        // Paper (5)
        for (int bpi1 = 2; bpi1< numSteps-1; bpi1++){
            for (int a1 = firstActionOfEachStep[bpi1]; a1 < firstActionOfEachStep[bpi1+1]; a1++){
                for (int bpi2 = bpi1; bpi2< numSteps-1; bpi2++){
                    for (int a2 = firstActionOfEachStep[bpi2]; a2 < firstActionOfEachStep[bpi2+1]; a2++){
                        if (a2 == a1){
                            continue;
                        }
                        for (int a3 = firstActionOfEachStep[bpi2]; a3 < goalAction; a3++){
                            if (a2 == a3){
                                continue;
                            }
                            addHardClauseTwoNegOneTrue(file, orderingArray[a1][a2], orderingArray[a2][a3], orderingArray[a1][a3]);
                            numClauses = numClauses+1;
                        }
                    }
                }
            }
        }

        // for (int a1 = 1; a1 <= numActions; a1++){
        //     // if (a1 == goalAction){
        //     //     continue;
        //     // }
        //     for (int a2 = 1; a2 <= numActions; a2++){
        //         // if (a2 == goalAction){
        //         //     continue;
        //         // }
        //         for (int a3 = 1; a3 <= numActions; a3++){
        //             // if (a3 == goalAction){
        //             //     continue;
        //             // }
        //             addHardClauseTwoNegOneTrue(file, orderingArray[a1][a2], orderingArray[a2][a3], orderingArray[a1][a3]);
        //             numClauses = numClauses+1;
        //         }
        //     }
        // }

        gettimeofday(&tp, NULL);
        long currentT = tp.tv_sec * 1000 + tp.tv_usec / 1000;
        getNumTime = getNumTime + currentT - startT;

        file << "c Paper Soft-Clauses" << endl;
        // Paper soft-clauses 1
        for (int a = 2; a < goalAction; a++)
        {
            addNegatedAction(file, a);
            numClauses++;
        }

        int oldClauses = numClauses;
        // support array
        int supportCounter = 1;
        vector<pair<int, int>> ***varToPrecToSupport = new vector<pair<int, int>> **[numActions + 1];

        for (int breakPointIndex = 1; breakPointIndex < numSteps - 1; breakPointIndex++)
        {
            for (int a = firstActionOfEachStep[breakPointIndex]; a < firstActionOfEachStep[breakPointIndex + 1]; a++)
            {
                int action = varActionToRealAction[a];
                varToPrecToSupport[a] = new vector<pair<int, int>> *[htn->numPrecs[action] + 1];
                for (int precIndex = 0; precIndex < htn->numPrecs[action] + 1; precIndex++)
                {
                    varToPrecToSupport[a][precIndex] = new vector<pair<int, int>>();
                }
                if (breakPointIndex == 1)
                {
                    varToPrecToSupport[a][htn->numPrecs[action]]->push_back(make_pair(1, supportCounter + numActions + orderingCounter));
                    supportCounter = supportCounter + 1;
                }
                else
                {
                    varToPrecToSupport[a][htn->numPrecs[action]]->push_back(make_pair(goalAction + breakPointIndex - 1, supportCounter + numActions + orderingCounter));
                    supportCounter = supportCounter + 1;
                }
                for (int addEffIndex = 0; addEffIndex < htn->numVars; addEffIndex++)
                {
                    if (n->state[addEffIndex])
                    {
                        if (addInDelInt(breakPointIndex, addEffIndex) != -1)
                        {
                            continue;
                        }
                        for (int precIndex = 0; precIndex < htn->numPrecs[action]; precIndex++)
                        {
                            if (addEffIndex == htn->precLists[action][precIndex])
                            {
                                varToPrecToSupport[a][precIndex]->push_back(make_pair(1, supportCounter + numActions + orderingCounter));
                                supportCounter = supportCounter + 1;
                            }
                        }
                    }
                }
                for (int precIndex = 0; precIndex < htn->numPrecs[action]; precIndex++)
                {
                    int prec = htn->precLists[action][precIndex];
                    int suppIndexStart = 2;
                    int temp = addInDelInt(breakPointIndex, prec);
                    if (temp != -1)
                    {
                        suppIndexStart = firstActionOfEachStep[2 + temp];
                    }
                    for (int suppIndex = suppIndexStart; suppIndex < firstActionOfEachStep[breakPointIndex + 1]; suppIndex++)
                    {
                        if (suppIndex == a)
                        {
                            continue;
                        }
                        int support = varActionToRealAction[suppIndex];
                        for (int addEffIndex = 0; addEffIndex < htn->numAdds[support]; addEffIndex++)
                        {
                            if (htn->addLists[support][addEffIndex] == prec)
                            {
                                varToPrecToSupport[a][precIndex]->push_back(make_pair(suppIndex, supportCounter + numActions + orderingCounter));
                                supportCounter = supportCounter + 1;
                            }
                        }
                    }
                }
            }
        }

        varToPrecToSupport[goalAction] = new vector<pair<int, int>> *[htn->gSize + 1];
        for (int precIndex = 0; precIndex < htn->gSize + 1; precIndex++)
        {
            varToPrecToSupport[goalAction][precIndex] = new vector<pair<int, int>>();
        }
        if (goalAction < numActions)
        {
            varToPrecToSupport[goalAction][htn->gSize]->push_back(make_pair(numActions, supportCounter + numActions + orderingCounter));
        }

        supportCounter = supportCounter + 1;
        for (int addEffIndex = 0; addEffIndex < htn->numVars; addEffIndex++)
        {
            if (n->state[addEffIndex])
            {
                if (addInDelInt(numSteps - 1, addEffIndex) != -1)
                {
                    continue;
                }
                for (int precIndex = 0; precIndex < htn->gSize; precIndex++)
                {
                    if (addEffIndex == htn->gList[precIndex])
                    {
                        varToPrecToSupport[goalAction][precIndex]->push_back(make_pair(1, supportCounter + numActions + orderingCounter));
                        supportCounter = supportCounter + 1;
                    }
                }
            }
        }

        for (int precIndex = 0; precIndex < htn->gSize; precIndex++)
        {
            int prec = htn->gList[precIndex];
            int suppIndexStart = 2;
            int temp = addInDelInt(numSteps - 1, prec);
            if (temp != -1)
            {
                suppIndexStart = firstActionOfEachStep[2 + temp];
            }
            for (int suppIndex = suppIndexStart; suppIndex < goalAction; suppIndex++)
            {
                int support = varActionToRealAction[suppIndex];
                for (int addEffIndex = 0; addEffIndex < htn->numAdds[support]; addEffIndex++)
                {
                    if (htn->addLists[support][addEffIndex] == prec)
                    {
                        varToPrecToSupport[goalAction][precIndex]->push_back(make_pair(suppIndex, supportCounter + numActions + orderingCounter));
                        supportCounter = supportCounter + 1;
                    }
                }
            }
        }

        for (int a = goalAction + 1; a <= numActions; a++)
        {
            varToPrecToSupport[a] = new vector<pair<int, int>> *[precsIntermediate[a - goalAction - 1].size() + 1];
            for (int precIndex = 0; precIndex < precsIntermediate[a - goalAction - 1].size() + 1; precIndex++)
            {
                varToPrecToSupport[a][precIndex] = new vector<pair<int, int>>();
            }
            if (a == goalAction + 1)
            {
                varToPrecToSupport[a][precsIntermediate[a - goalAction - 1].size()]->push_back(make_pair(1, supportCounter + numActions + orderingCounter));
                supportCounter = supportCounter + 1;
            }
            else
            {
                varToPrecToSupport[a][precsIntermediate[a - goalAction - 1].size()]->push_back(make_pair(a - 1, supportCounter + numActions + orderingCounter));
                supportCounter = supportCounter + 1;
            }
            for (int addEffIndex = 0; addEffIndex < htn->numVars; addEffIndex++)
            {
                if (n->state[addEffIndex])
                {
                    if (addInDelInt(a - goalAction, addEffIndex) != -1)
                    {
                        continue;
                    }
                    for (int precIndex = 0; precIndex < precsIntermediate[a - goalAction - 1].size(); precIndex++)
                    {
                        if (addEffIndex == precsIntermediate[a - goalAction - 1][precIndex])
                        {
                            varToPrecToSupport[a][precIndex]->push_back(make_pair(1, supportCounter + numActions + orderingCounter));
                            supportCounter = supportCounter + 1;
                        }
                    }
                }
            }
            for (int precIndex = 0; precIndex < precsIntermediate[a - goalAction - 1].size(); precIndex++)
            {
                int prec = precsIntermediate[a - goalAction - 1][precIndex];
                int suppIndexStart = 2;
                int temp = addInDelInt(a - goalAction, prec);
                if (temp != -1)
                {
                    suppIndexStart = firstActionOfEachStep[2 + temp];
                }
                for (int suppIndex = suppIndexStart; suppIndex < firstActionOfEachStep[a - goalAction + 1]; suppIndex++)
                {
                    int support = varActionToRealAction[suppIndex];
                    for (int addEffIndex = 0; addEffIndex < htn->numAdds[support]; addEffIndex++)
                    {
                        if (htn->addLists[support][addEffIndex] == prec)
                        {
                            varToPrecToSupport[a][precIndex]->push_back(make_pair(suppIndex, supportCounter + numActions + orderingCounter));
                            supportCounter = supportCounter + 1;
                        }
                    }
                }
            }
        }

        // for (int i = 0; i<varActionToRealAction.size(); i++){
        //     cout << i << ": " << varActionToRealAction[i]<< endl;
        // }
        // cout <<"-------------------" << endl;
        // for(int a = 2; a<goalAction; a++){
        //     cout << "Process Action " << a <<":"<<endl;
        //     int action = varActionToRealAction[a];
        //     for (int precIndex = 0; precIndex < htn->numPrecs[action]; precIndex++) {
        //         cout << "---Precondition " << htn->precLists[action][precIndex] <<":"<<endl<<"------";
        //         for (int adderIndex = 0; adderIndex < varToPrecToSupport[a][precIndex]->size(); adderIndex++){
        //             cout << "("<<varToPrecToSupport[a][precIndex]->at(adderIndex).first << ", " << varToPrecToSupport[a][precIndex]->at(adderIndex).second << "), ";
        //         }
        //         cout << endl;
        //     }
        //     cout << "---Precondition Special:"<<endl<<"------";
        //     for (int adderIndex = 0; adderIndex < varToPrecToSupport[a][htn->numPrecs[action]]->size(); adderIndex++){
        //         cout << varToPrecToSupport[a][htn->numPrecs[action]]->at(adderIndex).first << ", "<< varToPrecToSupport[a][htn->numPrecs[action]]->at(adderIndex).second;
        //     }
        //     cout << endl;
        // }

        // for(int a = goalAction+1; a<=numActions; a++){
        //     cout << "Process Intermediate Action " << a <<":"<<endl;
        //     int action = varActionToRealAction[a];
        //     for (int precIndex = 0; precIndex < precsIntermediate[a-1-goalAction].size(); precIndex++) {
        //         cout << "---Precondition " << precsIntermediate[a-1-goalAction][precIndex] <<":"<<endl<<"------";
        //         for (int adderIndex = 0; adderIndex < varToPrecToSupport[a][precIndex]->size(); adderIndex++){
        //             cout << varToPrecToSupport[a][precIndex]->at(adderIndex).first << ", ";
        //         }
        //         cout << endl;
        //     }
        //     cout << "---Precondition Special:"<<endl<<"------";
        //     for (int adderIndex = 0; adderIndex < varToPrecToSupport[a][precsIntermediate[a-1-goalAction].size()]->size(); adderIndex++){
        //         cout << varToPrecToSupport[a][precsIntermediate[a-1-goalAction].size()]->at(adderIndex).first << ", ";
        //     }
        //     cout << endl;
        // }

        // cout << "Process Goal " << ":"<<endl;
        //     for (int precIndex = 0; precIndex < htn->gSize; precIndex++) {
        //         cout << "---Precondition " << htn->gList[precIndex] <<":"<<endl<<"------";
        //         for (int adderIndex = 0; adderIndex < varToPrecToSupport[goalAction][precIndex]->size(); adderIndex++){
        //             cout << varToPrecToSupport[goalAction][precIndex]->at(adderIndex).first << ", ";
        //         }
        //         cout << endl;
        //     }
        //     cout << "---Precondition Special:"<<endl<<"------";
        //     for (int adderIndex = 0; adderIndex < varToPrecToSupport[goalAction][htn->gSize]->size(); adderIndex++){
        //         cout << varToPrecToSupport[goalAction][htn->gSize]->at(adderIndex).first << ", ";
        //     }
        //     cout << endl;

        // file << "c Paper 6" << endl;
        // // Paper(6)
        // if (numActions > goalAction){ //if we have no steps between init and goal we will have no deleters
        //     for (int breakPointIndex = 1; breakPointIndex < numSteps-2; breakPointIndex++){
        //         for (int a = firstActionOfEachStep[breakPointIndex]; a < firstActionOfEachStep[breakPointIndex+1]; a++){
        //             int action = varActionToRealAction[a];
        //             int varSuppAction = varToPrecToSupport[a][htn->numPrecs[action]]->back().first;
        //             int varDelAction = goalAction+breakPointIndex;
        //             addHardClauseTwoNegTwoTrue(file, varToPrecToSupport[a][htn->numPrecs[action]]->back().second, varDelAction, orderingArray[varDelAction][varSuppAction],
        //                 orderingArray[a][varDelAction]); //Could be handeled differntly because the delete Action needs to be true as well, so we could just
        //                 //use the orderings
        //             numClauses = numClauses +1;
        //         }
        //     }
        // } // For the paper: in 6 xak must be distinct from ai, otherwise this could block itsself

        file << "c Paper 7" << endl;
        // Paper (7)
        vector<int> helperVec;
        int helperVariableCounter = numActions + orderingCounter + supportCounter + 1;
        for (int a = 2; a <= numActions; a++)
        {
            int tempNumPrecs;
            if (a < goalAction)
            {
                tempNumPrecs = htn->numPrecs[varActionToRealAction[a]];
            }
            else if (a == goalAction)
            {
                continue;
            }
            else
            {
                tempNumPrecs = precsIntermediate[a - goalAction - 1].size();
            }
            for (int preIndex = 0; preIndex <= tempNumPrecs; preIndex++)
            {
                if (varToPrecToSupport[a][preIndex] != nullptr)
                {
                    if (varToPrecToSupport[a][preIndex]->size() == 0 && preIndex < tempNumPrecs && a < goalAction)
                    {
                        helperVec.clear();
                        // cout << "Does this happen? " << endl;
                        addHardClauseNeg(file, a);
                        numClauses = numClauses + 1;
                        continue;
                        // cout << "Size 0: " << a << " " << preIndex<< " " << tempNumPrecs << " " << htn->precLists[varActionToRealAction[a]][preIndex] << endl;
                        // for (int i = 0; i<htn->addToActionSize[htn->precLists[varActionToRealAction[a]][preIndex]];i++){
                        //     cout << "Supp by: " << htn->addToAction[htn->precLists[varActionToRealAction[a]][preIndex]][i] << endl;
                        // }
                    }
                    for (int adderIndex = 0; adderIndex < varToPrecToSupport[a][preIndex]->size(); adderIndex++)
                    {
                        helperVec.push_back(helperVariableCounter);
                        addHardClauseFirstNegSecTrue(file, helperVariableCounter, orderingArray[varToPrecToSupport[a][preIndex]->at(adderIndex).first][a]);
                        //addHardClauseFirstNegSecTrue(file, helperVariableCounter, varToPrecToSupport[a][preIndex]->at(adderIndex).second);
                        numClauses = numClauses + 2;
                        helperVariableCounter = helperVariableCounter + 1;
                    }
                    addHardClauseFirstNegVectorTrue(file, a, helperVec);
                    numClauses = numClauses + 1;
                    helperVec.clear();
                }
            }
        }

        file << "c Paper 7 Goal Action" << endl;
        for (int precIndex = 0; precIndex < htn->gSize + 1; precIndex++)
        {
            if (goalAction == numActions && precIndex == htn->gSize)
            {
                continue;
            }
            if (varToPrecToSupport[goalAction][precIndex] != nullptr)
            {
                for (int adderIndex = 0; adderIndex < varToPrecToSupport[goalAction][precIndex]->size(); adderIndex++)
                {
                    helperVec.push_back(orderingArray[varToPrecToSupport[goalAction][precIndex]->at(adderIndex).first][goalAction]);
                    //helperVec.push_back(helperVariableCounter);
                    //addHardClauseFirstNegSecTrue(file, helperVariableCounter, orderingArray[varToPrecToSupport[goalAction][precIndex]->at(adderIndex).first][goalAction]);
                    //addHardClauseFirstNegSecTrue(file, helperVariableCounter, varToPrecToSupport[goalAction][precIndex]->at(adderIndex).second);
                    //numClauses = numClauses + 2;
                    //helperVariableCounter = helperVariableCounter + 1;
                }
                addHardClauseFirstNegVectorTrue(file, goalAction, helperVec);
                numClauses = numClauses + 1;
                helperVec.clear();
            }
            else
            {
                // Unerfüllbar
                addHardClause(file, 1);
                addHardClauseNeg(file, 1);
                return;
            }
        }

        file.close();
        adapt(helperVariableCounter - 1, numClauses, hardClauseCost, filename);
        //        adapt(supportCounter + numActions + orderingCounter, numClauses, hardClauseCost, filename);

        // cout << "Goal has: "<<endl;
        // for (int precIndex = 0; precIndex < htn->gSize; precIndex++) {
        //     cout << "GList "<<precIndex<< ": " << htn->gList[precIndex] << endl;
        //     for (int i = 0; i<htn->addToActionSize[htn->gList[precIndex]];i++){
        //         cout << "Supp by: " << htn->addToAction[htn->gList[precIndex]][i] << endl;
        //     }
        // }
        // for (int addEffIndex = 0; addEffIndex < htn->numVars; addEffIndex++) {
        //         if (n->state[addEffIndex]){
        //             cout << "State has: " << addEffIndex<<endl;
        //         }
        //     }
        // for (int i = 0; i<varActionToRealAction.size(); i++){
        //     cout << i << ": " << varActionToRealAction[i]<< endl;
        // }

        // cout << "Precs of Intermediate: " << endl;
        // for (int a = goalAction+1; a <= numActions; a++){
        //     cout << precsIntermediate[a-goalAction-1].size()<<endl;
        // }
        // if (n->numAbstract > 0 && n->unconstraintAbstract[0]->task != numActions){
        //     exit(1);
        // }

        cout << "Num Clauses: " << numClauses << endl;

        for (int breakPointIndex = 1; breakPointIndex < numSteps - 1; breakPointIndex++)
        {
            for (int a = firstActionOfEachStep[breakPointIndex]; a < firstActionOfEachStep[breakPointIndex + 1]; a++)
            {
                int action = varActionToRealAction[a];
                for (int precIndex = 0; precIndex < htn->numPrecs[action] + 1; precIndex++)
                {
                    delete varToPrecToSupport[a][precIndex];
                }
                delete[] varToPrecToSupport[a];
            }
        }

        for (int precIndex = 0; precIndex < htn->gSize + 1; precIndex++)
        {
            delete varToPrecToSupport[goalAction][precIndex];
        }
        delete[] varToPrecToSupport[goalAction];

        if (numSteps > 2)
        {
            for (int interAction = 1; interAction < numSteps - 2; interAction++)
            {
                delete varToPrecToSupport[goalAction + interAction][0];
                delete[] varToPrecToSupport[goalAction + interAction];
            }
        }
        delete[] varToPrecToSupport;

        firstActionOfEachStep.clear();
        varActionToRealAction.clear();
        for (auto &innerVector : precsIntermediate)
        {
            innerVector.clear();
        }
        precsIntermediate.clear();
        for (auto &innerVector : delsIntermediate)
        {
            innerVector.clear();
        }
        delsIntermediate.clear();

        // cout << "Num Actions: " << numActions << endl;
        // cout << "Num Clauses: " << numClauses << endl;
        // cout << "Step 6+7 Percent of Clauses: " << fixed << setprecision(4) <<
        //     1-((oldClauses) / static_cast<double>(numClauses)) << endl;
        // cout << "Step 5 Percent of Clauses: " << fixed << setprecision(4) <<
        //     ((oldClauses- s5Clauses) / static_cast<double>(numClauses)) << endl;
        // cout << "Step 1-4 Percent of Clauses: " << fixed << setprecision(4) <<
        //     ((s5Clauses) / static_cast<double>(numClauses)) << endl;
    }

public:
    long buildTime = 0;
    long calcTime = 0;
    long getNumTime = 0;
    // Heuristic* heurica;
    // bool tempCounter = false;

    satRC2(Model *htnModel, int index) : Heuristic(htnModel, index)
    {
        htn = htnModel;
        // heurica = new hhRC2<hsAddFF>(htn, 2, estMIXED, false);
        // ((hhRC2<hsAddFF>*)heurica)->sasH->heuristic = sasAdd;
    }

    string getDescription()
    {
        return "satRC2";
    }

    void setHeuristicValue(searchNode *n, searchNode *parent, int action) override
    {
        // heurica->setHeuristicValue(n, parent, action);
        setHeuristicValue(n, parent);
    }

    void setHeuristicValue(searchNode *n, searchNode *parent, int absTask, int method) override
    {
        // heurica->setHeuristicValue(n, parent, absTask, method);
        setHeuristicValue(n, parent);
    }

    void setHeuristicValue(searchNode *n, searchNode *parent)
    {
        // bool temp = n->goalReachable;
        // cout << "Old Heurica: " << n->heuristicValue[2]<<endl;

        if (n->numAbstract == 0 && n->numPrimitive == 0)
        {
            n->heuristicValue[index] = 0;
            return;
        }

        timeval tp;
        gettimeofday(&tp, NULL);
        long startT = tp.tv_sec * 1000 + tp.tv_usec / 1000;

        makeFile("../RamDisk/SatFile.wcnf", n);

        gettimeofday(&tp, NULL);
        long currentT = tp.tv_sec * 1000 + tp.tv_usec / 1000;
        buildTime = buildTime + currentT - startT;

        n->heuristicValue[index] = exec("../EvalMaxSAT/build/EvalMaxSAT_bin ../RamDisk/SatFile.wcnf");

        gettimeofday(&tp, NULL);
        long secondT = tp.tv_sec * 1000 + tp.tv_usec / 1000;
        calcTime = calcTime + secondT - currentT;

        cout << "Time Cost for building: " << buildTime << endl;
        cout << "Time Cost for solving: " << calcTime << endl;
        cout << "Time Cost for Step 5: " << getNumTime << endl;
        cout << "For Value: " << n->heuristicValue[index] << endl;
        cout << "----------------" << endl;

        if (n->heuristicValue[index] == -1)
        {
            n->goalReachable = false;
            n->heuristicValue[index] = UNREACHABLE;
        }

        // if (temp != n->goalReachable && temp){
        //     if (tempCounter){
        //         exit(1);
        //     } else {
        //         tempCounter = true;
        //     }
        // }
    }
};
// public:
// Heuristic* heurica;

//     satRC2(Model *htnModel, int index) : Heuristic(htnModel, index){
//         htn = htnModel;
//         heurica = new hhRC2<hsAddFF>(htn, 2, estMIXED, false);
// 		((hhRC2<hsAddFF>*)heurica)->sasH->heuristic = sasAdd;
//     }

//     string getDescription(){
// 		return "satRC2";
// 	}

//     void setHeuristicValue(searchNode *n, searchNode *parent, int action) override {
//         setHeuristicValue(n, parent);
//         // if (!n->goalReachable){
//         //     cout << "---> ?" << endl;
//         //     n->goalReachable=true;
//         //     test = true;
//         // }
//         heurica->setHeuristicValue(n, parent, action);
//         // if (!n->goalReachable){
//         //     cout << "y" << endl;
//         // } else {
//         //     cout << "n" << endl;
//         //     if (test){
//         //         helperNode(n);
//         //         exit(1);
//         //     }
//         // }
//     }

//     void helperNode(searchNode *n) {
//         planStep* temp;
//         if(n->numAbstract > 0){
//             temp = n->unconstraintAbstract[0];
//         } else if (n->numPrimitive > 0) {
//             temp = n->unconstraintPrimitive[0];
//         } else {
//             return ;
//         }

//         cout << temp->task<<endl;

//         while (temp->numSuccessors > 0){
//             temp = temp->successorList[0];
//             cout << temp->task<<endl;
//         }

//         for (int i = 0; i < htn->numStateBits; i++){
//             if (n->state[i]) cout <<i<<";";
//         }
//         cout << endl;

//         return;
//     }

//     void setHeuristicValue(searchNode *n, searchNode *parent, int absTask, int method) override {
//         //bool test = false;
//         setHeuristicValue(n, parent);
//         // if (!n->goalReachable){
//         //     cout << "---> ?" << endl;
//         //     n->goalReachable=true;
//         //     test = true;
//         // }
//         heurica->setHeuristicValue(n, parent, absTask, method);
//         // if (!n->goalReachable){
//         //     cout << "y" << endl;
//         // } else {
//         //     cout << "n" << endl;
//         //     if (test){
//         //         helperNode(n);
//         //         cout << n->heuristicValue[2]<< "; "<< n->heuristicValue[0]<< endl;
//         //         exit(1);
//         //     }
//         // }
//     }

//     void setHeuristicValue(searchNode *n, searchNode *parent) {
//             varActionToRealAction.clear();

//         timeval tp;
//         gettimeofday(&tp, NULL);
//         long startT = tp.tv_sec * 1000 + tp.tv_usec / 1000;

//         makeFile("../RamDisk/SatFile.wcnf", n);

//         gettimeofday(&tp, NULL);
//         long currentT = tp.tv_sec * 1000 + tp.tv_usec / 1000;

//         n->heuristicValue[index] = 0 - exec("../loandra/loandra ../RamDisk/SatFile.wcnf");

//         cout << "Time Cost: "<<(currentT - startT)  << "; For Value: ";

//         cout << n->heuristicValue[index] << endl;
//         //exit(1);

//         if (n->heuristicValue[index]==2147483647){
//              n->goalReachable=false;
//         }
//     }

// };

// //old try
// class satRC2 : public Heuristic {
// private:
// int actionCost;
// int hardClauseCost;
// vector<int> varActionToRealAction;
// vector<int> varStepBreakPoints;
// vector<int>* realActionToVarAction;
// Model* htn;
// bool test=false;

// int exec(const char* cmd) {  //taken from stackoverflow and adapted
//     std::array<char, 128> buffer;
//     std::unique_ptr<FILE, decltype(&pclose)> pipe(popen((std::string(cmd) + " 2>/dev/null").c_str(), "r"), pclose);
//     if (!pipe) {
//         throw std::runtime_error("popen() failed!");
//     }
//     while (fgets(buffer.data(), buffer.size(), pipe.get()) != nullptr) {
//         if (buffer[0] == 'o') {
//             return round(stol((buffer.data()+2)));
//         }
//     }
//     return 2147483647;
// }

// void adapt(int numVars, int numClauses, int maxCost, const std::string& filename){
//     std::fstream file(filename, std::ios::in | std::ios::out);

//     file.seekp(0);
//     file.write(pad_string_to_32_bytes("p wcnf " + to_string(numVars) + " " + to_string(numClauses) + " " + to_string(maxCost) ).c_str(), 32);

//     file.close();
// }

// string pad_string_to_32_bytes(const std::string& input)//taken from chatgpt
// {
//     std::ostringstream oss;
//     oss << input;
//     int num_spaces = 32 - input.length() - 1; // Subtract 1 for the newline character
//     for (int i = 0; i < num_spaces; ++i) {
//         oss << " ";
//     }
//     oss << '\n';
//     return oss.str();
// }

// // int getNumActions(searchNode *n) {
// //     planStep* temp;
// //     if(n->numAbstract > 0){
// //         temp = n->unconstraintAbstract[0];
// //     } else if (n->numPrimitive > 0) {
// //         temp = n->unconstraintPrimitive[0];
// //     } else {
// //         return -1;
// //     }

// //     realActionToVarAction = new vector<int>[htn->numActions];
// //     int result = 2; //Initial and Goal Action
// //     varActionToRealAction.push_back(-1);
// //     varActionToRealAction.push_back(-1);
// //     varActionToRealAction.push_back(-1); // added one in addition so that the numbers of the vars actually match
// //     varStepBreakPoints.push_back(3); // First task beginns at 3

// //     for (int j = 0; j < temp->numReachableT; j++) {
// //         if (temp->reachableT[j] < htn->numActions){
// //             result++;
// //             varActionToRealAction.push_back(temp->reachableT[j]);
// //             realActionToVarAction[temp->reachableT[j]].push_back(result);
// //         }
// //     }
// //     varStepBreakPoints.push_back(result+1);

// //     while (temp->numSuccessors > 0){
// //         temp = temp->successorList[0];
// //         for (int j = 0; j < temp->numReachableT; j++) {
// //             if (temp->reachableT[j] < htn->numActions){
// //                 result++;
// //                 varActionToRealAction.push_back(temp->reachableT[j]);
// //                 realActionToVarAction[temp->reachableT[j]].push_back(result);
// //             }
// //         }
// //         varStepBreakPoints.push_back(result+1);
// //     }
// //     return result;
// // }

// int getNumActions(searchNode *n) {
//     planStep* temp;
//     if(n->numAbstract > 0){
//         temp = n->unconstraintAbstract[0];
//     } else if (n->numPrimitive > 0) {
//         temp = n->unconstraintPrimitive[0];
//     } else {
//         return -1;
//     }

//     realActionToVarAction = new vector<int>[htn->numActions];
//     int result = 1; //Initial and Goal Action
//     varActionToRealAction.push_back(-1);
//     varActionToRealAction.push_back(-1); // added one in addition so that the numbers of the vars actually match
//     varStepBreakPoints.push_back(2); // First task beginns at 2

//     for (int j = 0; j < temp->numReachableT; j++) {
//         if (temp->reachableT[j] < htn->numActions){
//             result++;
//             varActionToRealAction.push_back(temp->reachableT[j]);
//             realActionToVarAction[temp->reachableT[j]].push_back(result);
//         }
//     }
//     varStepBreakPoints.push_back(result+1);

//     while (temp->numSuccessors > 0){
//         temp = temp->successorList[0];
//         for (int j = 0; j < temp->numReachableT; j++) {
//             if (temp->reachableT[j] < htn->numActions){
//                 result++;
//                 varActionToRealAction.push_back(temp->reachableT[j]);
//                 realActionToVarAction[temp->reachableT[j]].push_back(result);
//             }
//         }
//         varStepBreakPoints.push_back(result+1);
//     }
//     varActionToRealAction.push_back(-1);
//     result++;
//     return result;
// }

// void addHardClause(std::ofstream& file, int variable) {
//     file << hardClauseCost << " " << variable << " 0" << endl;
// }

// void addHardClauseNeg(std::ofstream& file, int variable) {
//     file << hardClauseCost << " -" << variable << " 0" << endl;
// }

// void addHardClause(std::ofstream& file, string clause) {
//     file << hardClauseCost << " " << clause << " 0" << endl;
// }

// void addAction(std::ofstream& file, int action) {
//     file << actionCost << " -" << action << " 0" << endl;
// }

// void addOrdering(std::ofstream& file, int orderingNumber) {
//     file << "1 -" << orderingNumber  << " 0" << endl;
// }

// // void makeFile(const std::string& filename, searchNode *n) {
// //     int numActions = getNumActions(n);
// //     if (numActions == -1){
// //         return;
// //     }
// //     actionCost = numActions*numActions + 1;
// //     hardClauseCost = actionCost+1;
// //     int numClauses = 0;

// //     // Variable Structure:
// //     // First initial action then goal action (2)
// //     // Then all action
// //     // Then for all action follows a block of numAction to represent k(ai,aj)
// //     // First all j are cycled and then the i is

// //     ofstream file(filename);
// //     if (!file) {
// //         cerr << "Error: Could not open file." << std::endl;
// //         return;
// //     }

// //     file << pad_string_to_32_bytes("Hello There");

// //     for (int i = 1; i < numActions+1; i++){
// //         addAction(file,i);                                               // added negated actions as soft clauses
// //         addHardClauseNeg(file,(i*numActions) + i);                       // ordering constraints from ai to ai, paper (1)
// //     }
// //     numClauses = numClauses + 2*numActions;

// //     for (int i = 1; i < actionCost; i++){
// //         addOrdering(file,i+numActions);                                  // added negated ordering constraints as soft clauses
// //     }
// //     numClauses = numClauses + actionCost-1;

// //     addHardClause(file,1);
// //     addHardClause(file,2);                                               // paper (2), inital and goal action must exist
// //     numClauses = numClauses + 2;

// //     for (int i = 1; i < numActions+1; i++){
// //         for (int j = 1; j < numActions+1; j++){
// //             addHardClause(file,"-" + to_string((numActions*i)+j) + " " + to_string(i));        // paper 3
// //             addHardClause(file,"-" + to_string((numActions*i)+j) + " " + to_string(j));        // paper 3
// //         }
// //     }
// //     numClauses = numClauses + 2*(actionCost-1);

// //     for (int i = 3; i < numActions+1; i++){
// //         addHardClause(file,"-" + to_string(i) + " " + to_string(numActions+i));                // paper 4
// //         addHardClause(file,"-" + to_string(i) + " " + to_string((i * numActions) + 2));        // paper 4
// //     }
// //     numClauses = numClauses + 2*(numActions - 2);

// //     for (int i = 1; i < numActions+1; i++){
// //         for (int j = 1; j < numActions+1; j++){
// //             for (int k = 1; k < numActions+1; k++){
// //                 addHardClause(file,"-" + to_string((i * numActions)+j) + " -" + to_string((j * numActions)+k) + " " + to_string((i * numActions)+k));        // paper 5
// //             }
// //         }
// //     }
// //     numClauses = numClauses + (numActions * numActions * numActions);

// //     file << "c Start Last part"<<endl;

// //     //delete relaxiert -> Kein Thread möglich.
// //     // causal link can only exist if the first action is part of this planning step or of one before this one
// //     int lastBreakPoint = 3;
// //     for (int i = 1; i < varStepBreakPoints.size(); i++){
// //         for (int j = lastBreakPoint; j < varStepBreakPoints[i]; j++){
// //             int realAction = varActionToRealAction[j];

// //             for (int precIndex = 0; precIndex < htn->numPrecs[realAction]; precIndex++){
// //                 int prec = htn->precLists[realAction][precIndex];
// //                 string clause = "-" + to_string(j);
// //                 for (int addActionIndex = 0; addActionIndex < htn->addToActionSize[prec]; addActionIndex++){
// //                     int addAction = htn->addToAction[prec][addActionIndex];
// //                     for (int adder : realActionToVarAction[addAction]){
// //                         if (adder < varStepBreakPoints[i]){
// //                             clause = clause + " " + to_string((adder*numActions)+j);
// //                         }
// //                     }
// //                 }
// //                 if (n->state[prec]) {
// //                     clause = clause + " " + to_string(numActions+j);
// //                 }

// //                 addHardClause(file,clause);
// //                 numClauses++;
// //             }
// //         }
// //     }

// //     for (int goalIndex = 0; goalIndex < htn->gSize; goalIndex++){
// //         int goal = htn->gList[goalIndex];
// //         string clause = "-" + to_string(2);
// //         for (int addActionIndex = 0; addActionIndex < htn->addToActionSize[goal]; addActionIndex++){
// //             int addAction = htn->addToAction[goal][addActionIndex];
// //             for (int adder : realActionToVarAction[addAction]){
// //                 clause = clause + " " + to_string((adder*numActions)+2);
// //             }
// //         }
// //         if (n->state[goal]) {
// //             clause = clause + " " + to_string(numActions+2);
// //         }
// //         addHardClause(file,clause);
// //         numClauses++;
// //     }

// //     file.close();
// //     adapt(numActions + actionCost - 1, numClauses, hardClauseCost, filename);
// //     delete[] realActionToVarAction;
// //     //varActionToRealAction.clear();
// //     varStepBreakPoints.clear();
// // }

// void makeFile(const std::string& filename, searchNode *n) {
//     int numActions = getNumActions(n);
//     if (numActions == -1){
//         return;
//     }
//     actionCost = numActions*numActions + 1;
//     hardClauseCost = actionCost+1;
//     int numClauses = 0;
//     int numOrderings;
//     vector<int> varToOrderingBegin; //maps action i (index i-1) to its first ordering variable

//     // Variable Structure:
//     // First initial action then
//     // Then all action
//     // goal action
//     // Then for all action follows a block of numAction to represent  the ordering constraint going towards them k(aj,ai)
//     // First all j are cycled and then the i is

//     ofstream file(filename);
//     if (!file) {
//         cerr << "Error: Could not open file." << std::endl;
//         return;
//     }

//     file << pad_string_to_32_bytes("Hello There");

//     for (int i = 2; i < numActions; i++){
//         addAction(file,i);                                               // added negated actions as soft clauses
//     }
//     numClauses = numClauses + numActions - 2;

//     int counter = numActions;
//     int lastBreakpoint = 1;
//     for (int breakPointIndex = 0; breakPointIndex < varStepBreakPoints.size(); breakPointIndex++){
//         for (int i = lastBreakpoint; i< varStepBreakPoints[breakPointIndex]; i++){
//             varToOrderingBegin.push_back(counter+1);
//             for (int j = lastBreakpoint; j < numActions+1; j++){
//                 addOrdering(file, ++counter);                                  // added negated ordering constraints as soft clauses

//                 if (i == j){
//                     addHardClauseNeg(file, counter);                       // ordering constraints from ai to ai, paper (1)
//                 }
//             }
//         }
//         lastBreakpoint = varStepBreakPoints[breakPointIndex];
//     }
//     varToOrderingBegin.push_back(counter+1);
//     numClauses = numClauses + numActions - 1;
//     numOrderings = counter - numActions;
//     numClauses = numClauses + numOrderings;

//     addHardClause(file, 1);
//     addHardClause(file, numActions);                                               // paper (2), inital and goal action must exist
//     numClauses = numClauses + 2;

//     for (int i = 1; i < numActions; i++){
//         int temp = numActions + varToOrderingBegin[i-1];
//         for (int j = varToOrderingBegin[i-1]; j < varToOrderingBegin[i]; j++){
//             addHardClause(file,"-" + to_string(j) + " " + to_string(i));                       // paper 3
//             addHardClause(file,"-" + to_string(j) + " " + to_string(temp-j));      // paper 3
//         }
//         numClauses = numClauses + 2*(varToOrderingBegin[i]-varToOrderingBegin[i-1]);
//     }

//     for (int i = 2; i < numActions; i++){
//         addHardClause(file,"-" + to_string(i) + " " + to_string(numActions+i));                // paper 4
//         addHardClause(file,"-" + to_string(i) + " " + to_string(varToOrderingBegin[i]-1));        // paper 4
//     }
//     numClauses = numClauses + 2*(numActions - 2);

//     int test = numClauses;
//         timeval tp;
//         gettimeofday(&tp, NULL);
//         long startT = tp.tv_sec * 1000 + tp.tv_usec / 1000;

//     for (int i = 1; i < numActions+1; i++){
//         int numJ = (varToOrderingBegin[i] - varToOrderingBegin[i-1]);
//         int firstJ = numActions - (numJ -1);
//         for (int j = firstJ; j < numActions; j++){
//             int jOffset = j-(numActions-numJ);
//             for (int k = varToOrderingBegin[j-1]; k < varToOrderingBegin[j]; k++){
//                 int kOffsetJ = k - varToOrderingBegin[j-1] + 1;
//                 int actionK = numActions - (varToOrderingBegin[j] - varToOrderingBegin[j-1]) + kOffsetJ;
//                 if (actionK >= firstJ){
//                     addHardClause(file,"-" + to_string(varToOrderingBegin[i-1]+jOffset) + " -" + to_string(k) + " " +  to_string(varToOrderingBegin[i-1] + actionK - firstJ + 1));        // paper 5
//                     numClauses++;
//                 }
//             }
//         }
//     }

//      gettimeofday(&tp, NULL);
//         long currentT = tp.tv_sec * 1000 + tp.tv_usec / 1000;

//         cout << "Time Cost: "<<(currentT - startT)  << endl;

//     cout<< numClauses -test << endl;
//     float result = static_cast<float>(test) / numClauses;  // Perform floating-point division

//     std::cout << std::fixed << std::setprecision(2);

//     cout << result << endl;
//     cout << numClauses << endl;
//     cout << "end";

//     file << "c Start Last part"<<endl;

//     //delete relaxiert -> Kein Thread möglich.
//     // causal link can only exist if the first action is part of this planning step or of one before this one
//     int lastBreakPoint = 3;
//     for (int i = 1; i < varStepBreakPoints.size(); i++){
//         for (int j = lastBreakPoint; j < varStepBreakPoints[i]; j++){
//             int realAction = varActionToRealAction[j];

//             for (int precIndex = 0; precIndex < htn->numPrecs[realAction]; precIndex++){
//                 int prec = htn->precLists[realAction][precIndex];
//                 string clause = "-" + to_string(j);
//                 for (int addActionIndex = 0; addActionIndex < htn->addToActionSize[prec]; addActionIndex++){
//                     int addAction = htn->addToAction[prec][addActionIndex];
//                     for (int adder : realActionToVarAction[addAction]){
//                         if (adder < varStepBreakPoints[i]){
//                             clause = clause + " " + to_string((adder*numActions)+j);
//                         }
//                     }
//                 }
//                 if (n->state[prec]) {
//                     clause = clause + " " + to_string(numActions+j);
//                 }

//                 addHardClause(file,clause);
//                 numClauses++;
//             }
//         }
//     }

//     for (int goalIndex = 0; goalIndex < htn->gSize; goalIndex++){
//         int goal = htn->gList[goalIndex];
//         string clause = "-" + to_string(2);
//         for (int addActionIndex = 0; addActionIndex < htn->addToActionSize[goal]; addActionIndex++){
//             int addAction = htn->addToAction[goal][addActionIndex];
//             for (int adder : realActionToVarAction[addAction]){
//                 clause = clause + " " + to_string((adder*numActions)+2);
//             }
//         }
//         if (n->state[goal]) {
//             clause = clause + " " + to_string(numActions+2);
//         }
//         addHardClause(file,clause);
//         numClauses++;
//     }

//     file.close();
//     adapt(numActions + actionCost - 1, numClauses, hardClauseCost, filename);
//     delete[] realActionToVarAction;
//     varActionToRealAction.clear();
//     varStepBreakPoints.clear();
// }

// public:
// Heuristic* heurica;

//     satRC2(Model *htnModel, int index) : Heuristic(htnModel, index){
//         htn = htnModel;
//         heurica = new hhRC2<hsAddFF>(htn, 2, estMIXED, false);
// 		((hhRC2<hsAddFF>*)heurica)->sasH->heuristic = sasAdd;
//     }

//     string getDescription(){
// 		return "satRC2";
// 	}

//     void setHeuristicValue(searchNode *n, searchNode *parent, int action) override {
//         setHeuristicValue(n, parent);
//         // if (!n->goalReachable){
//         //     cout << "---> ?" << endl;
//         //     n->goalReachable=true;
//         //     test = true;
//         // }
//         heurica->setHeuristicValue(n, parent, action);
//         // if (!n->goalReachable){
//         //     cout << "y" << endl;
//         // } else {
//         //     cout << "n" << endl;
//         //     if (test){
//         //         helperNode(n);
//         //         exit(1);
//         //     }
//         // }
//     }

//     void helperNode(searchNode *n) {
//         planStep* temp;
//         if(n->numAbstract > 0){
//             temp = n->unconstraintAbstract[0];
//         } else if (n->numPrimitive > 0) {
//             temp = n->unconstraintPrimitive[0];
//         } else {
//             return ;
//         }

//         cout << temp->task<<endl;

//         while (temp->numSuccessors > 0){
//             temp = temp->successorList[0];
//             cout << temp->task<<endl;
//         }

//         for (int i = 0; i < htn->numStateBits; i++){
//             if (n->state[i]) cout <<i<<";";
//         }
//         cout << endl;

//         return;
//     }

//     void setHeuristicValue(searchNode *n, searchNode *parent, int absTask, int method) override {
//         //bool test = false;
//         setHeuristicValue(n, parent);
//         // if (!n->goalReachable){
//         //     cout << "---> ?" << endl;
//         //     n->goalReachable=true;
//         //     test = true;
//         // }
//         heurica->setHeuristicValue(n, parent, absTask, method);
//         // if (!n->goalReachable){
//         //     cout << "y" << endl;
//         // } else {
//         //     cout << "n" << endl;
//         //     if (test){
//         //         helperNode(n);
//         //         cout << n->heuristicValue[2]<< "; "<< n->heuristicValue[0]<< endl;
//         //         exit(1);
//         //     }
//         // }
//     }

//     void setHeuristicValue(searchNode *n, searchNode *parent) {
//             varActionToRealAction.clear();

//         timeval tp;
//         gettimeofday(&tp, NULL);
//         long startT = tp.tv_sec * 1000 + tp.tv_usec / 1000;

//         makeFile("../RamDisk/SatFile.wcnf", n);

//         gettimeofday(&tp, NULL);
//         long currentT = tp.tv_sec * 1000 + tp.tv_usec / 1000;

//         n->heuristicValue[index] = 0 - exec("../loandra/loandra ../RamDisk/SatFile.wcnf");

//         cout << "Time Cost: "<<(currentT - startT)  << "; For Value: ";

//         cout << n->heuristicValue[index] << endl;
//         //exit(1);

//         if (n->heuristicValue[index]==2147483647){
//              n->goalReachable=false;
//         }
//     }

// };
