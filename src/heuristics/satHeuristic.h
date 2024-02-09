#include "Heuristic.h"
#include "../Model.h"
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
#include <string.h>

namespace progression
{
    class satHeuristic : public Heuristic
    {
    private:
        int actionCost;
        int hardClauseCost;
        //[step][number of reachable actions]first(SAT var)second(HTN action)
        vector<vector<pair<int, int>>> stepToActionsVarReal;
        // Actions before step (Therefore step+1 entrys, because after the last step there are still action)
        //[step]first(SAT var effect Action)second(SAT var precondition Action)
        vector<pair<int, int>> artificiallyActionsBeforeStep;
        int numSteps;
        int numActions;
        int numOrderingAndActionVars;
        //[firstSATVar][secondSATVar]SATVar of ordering or -1 if it can not exist. First ordered before second.
        int **orderingArray;

        // vector<int> varActionToRealAction;
        // vector<int> firstActionOfEachStep;
        vector<vector<int>> precsArtificial;
        vector<vector<int>> delsArtificial;
        vector<int> initalActionAdds;
        Model *htn;

        int exec(const char *cmd)
        { // taken from stackoverflow and adapted
            std::array<char, 128> buffer;
            long int res = -1;
            std::unique_ptr<FILE, decltype(&pclose)> pipe(popen((std::string(cmd) + " 2>1 ; echo \"exitcode \"$?").c_str(), "r"), pclose);
            if (!pipe)
            {
                throw std::runtime_error("popen() failed!");
            }
            while (fgets(buffer.data(), buffer.size(), pipe.get()) != nullptr)
            {
                //cout << buffer.data() << endl;
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
                else if (strncmp(buffer.data(), "exitcode", strlen("exitcode")) == 0)
                {
                    if (strcmp(buffer.data() + 9, "0\n") != 0)
                    {
                        cout << "Something went wrong with EvalMaxSat" << endl;
                        exit(-1);
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

        vector<int> getPreconditions(int task)
        {
            vector<int> preconditions;
            if (task < htn->numActions)
            {
                for (int i = 0; i < htn->numPrecs[task]; i++)
                {
                    preconditions.push_back(htn->precLists[task][i]);
                }
            }
            else
            {
                for (int prec : htn->preconditions[task - htn->numActions])
                {
                    preconditions.push_back(prec);
                }
            }
            return preconditions;
        }

        vector<int> getDeletes(int task)
        {
            vector<int> deletes;
            if (task < htn->numActions)
            {
                for (int i = 0; i < htn->numDels[task]; i++)
                {
                    deletes.push_back(htn->delLists[task][i]);
                }
            }
            else
            {
                for (int del : htn->eff_negative[task - htn->numActions])
                {
                    deletes.push_back(del);
                }
            }
            return deletes;
        }

        vector<pair<int, int>> getReach(int task)
        {
            vector<pair<int, int>> reach;
            for (int j = 0; j < htn->numReachable[task]; j++)
            {
                reach.push_back(make_pair(numActions, htn->reachable[task][j]));
                numActions++;
            }
            return reach;
        }

        void populateDataStructures(searchNode *n)
        {
            planStep *temp;
            numSteps = 0;
            numActions = 1;
            if (n->numAbstract > 0)
            {
                temp = n->unconstraintAbstract[0];
            }
            else if (n->numPrimitive > 0)
            {
                temp = n->unconstraintPrimitive[0];
            }
            numSteps++;

            artificiallyActionsBeforeStep.push_back(make_pair(numActions, numActions + 1));
            numActions += 2;

            for (int addIndex = 0; addIndex < htn->numVars; addIndex++)
            {
                if (n->state[addIndex])
                {
                    initalActionAdds.push_back(addIndex);
                }
            }

            // inital Action does not delete anything
            delsArtificial.push_back(vector<int>());

            precsArtificial.push_back(getPreconditions(temp->task));
            stepToActionsVarReal.push_back(getReach(temp->task));
            delsArtificial.push_back(getDeletes(temp->task));

            while (temp->numSuccessors > 0)
            {
                numSteps++;
                temp = temp->successorList[0];
                artificiallyActionsBeforeStep.push_back(make_pair(numActions, numActions + 1));
                numActions += 2;
                precsArtificial.push_back(getPreconditions(temp->task));
                stepToActionsVarReal.push_back(getReach(temp->task));
                delsArtificial.push_back(getDeletes(temp->task));
            }

            artificiallyActionsBeforeStep.push_back(make_pair(numActions, numActions + 1));
            numActions += 2;

            vector<int> goalAtoms;
            for (int gIndex = 0; gIndex < htn->gSize; gIndex++)
            {
                goalAtoms.push_back(htn->gList[gIndex]);
            }
            precsArtificial.push_back(goalAtoms);

            numActions -= 1;

            // ordering Array
            orderingArray = new int *[numActions + 1];
            // populate with -1 for all orderings that can not exist.
            for (int a1 = 1; a1 <= numActions; a1++)
            {
                orderingArray[a1] = new int[numActions + 1];
                for (int a2 = 1; a2 <= numActions; a2++)
                {
                    orderingArray[a1][a2] = -1;
                }
            }
            // populate with actual SATVars for Orderings that can exist.
            numOrderingAndActionVars = numActions + 1;
            for (int outerStep = 0; outerStep < numSteps; outerStep++)
            {
                // ordering each intermediate effect action before the same intermediate preconditon action
                orderingArray[artificiallyActionsBeforeStep[outerStep].first][artificiallyActionsBeforeStep[outerStep].second] = numOrderingAndActionVars;
                numOrderingAndActionVars++;

                for (int innerStep = outerStep; innerStep < numSteps; innerStep++)
                {
                    for (pair<int, int> rAPairInner : stepToActionsVarReal[innerStep])
                    {
                        // ordering intermediate Actions of outerStep before reachable Actions of inner Step
                        orderingArray[artificiallyActionsBeforeStep[outerStep].first][rAPairInner.first] = numOrderingAndActionVars;
                        numOrderingAndActionVars++;
                        orderingArray[artificiallyActionsBeforeStep[outerStep].second][rAPairInner.first] = numOrderingAndActionVars;
                        numOrderingAndActionVars++;
                        // ordering reachable Actions of outerStep before reachable Actions of innerStep
                        for (pair<int, int> rAPairOuter : stepToActionsVarReal[outerStep])
                        {
                            orderingArray[rAPairOuter.first][rAPairInner.first] = numOrderingAndActionVars;
                            numOrderingAndActionVars++;
                        }
                    }
                    // ordering intermediate Actions of outerStep before intermediate Actions of innerStep
                    orderingArray[artificiallyActionsBeforeStep[outerStep].first][artificiallyActionsBeforeStep[innerStep + 1].first] = numOrderingAndActionVars;
                    numOrderingAndActionVars++;
                    orderingArray[artificiallyActionsBeforeStep[outerStep].first][artificiallyActionsBeforeStep[innerStep + 1].second] = numOrderingAndActionVars;
                    numOrderingAndActionVars++;
                    orderingArray[artificiallyActionsBeforeStep[outerStep].second][artificiallyActionsBeforeStep[innerStep + 1].first] = numOrderingAndActionVars;
                    numOrderingAndActionVars++;
                    orderingArray[artificiallyActionsBeforeStep[outerStep].second][artificiallyActionsBeforeStep[innerStep + 1].second] = numOrderingAndActionVars;
                    numOrderingAndActionVars++;
                    // ordering reachable Actions of outerStep before intermediate Actions of innerStep
                    for (pair<int, int> rAPairOuter : stepToActionsVarReal[outerStep])
                    {
                        orderingArray[rAPairOuter.first][artificiallyActionsBeforeStep[innerStep + 1].first] = numOrderingAndActionVars;
                        numOrderingAndActionVars++;
                        orderingArray[rAPairOuter.first][artificiallyActionsBeforeStep[innerStep + 1].second] = numOrderingAndActionVars;
                        numOrderingAndActionVars++;
                    }
                }
            }
            // ordering last intermediate effect action before the goalAction
            orderingArray[artificiallyActionsBeforeStep[numSteps].first][artificiallyActionsBeforeStep[numSteps].second] = numOrderingAndActionVars;
        }

        bool findIntInVector(vector<int> vec, int toFind)
        {
            if (std::find(vec.begin(), vec.end(), toFind) != vec.end())
            {
                return true;
            }
            return false;
        }

        int getLastDeletionUpToStep(int prec, int upperStep)
        {
            if (upperStep == 0)
            {
                return 0;
            }
            for (int currentStep = upperStep; currentStep > 0; currentStep--)
            {
                if (findIntInVector(delsArtificial[currentStep], prec))
                {
                    return currentStep;
                }
            }
            return 0;
        }

        bool varInAddOfAction(int var, int action)
        {
            if (htn->numAdds[action] == 0)
            {
                return false;
            }
            for (int addsIndex = 0; addsIndex < htn->numAdds[action]; addsIndex++)
            {
                if (var == htn->addLists[action][addsIndex])
                {
                    return true;
                }
            }
            return false;
        }

        void makeSATFile(const std::string &filename, searchNode *n)
        {
            populateDataStructures(n);
            cout << "Num Steps: " << numSteps << endl;
            cout << "Num Actions: " << numActions << endl;
            cout << "Num Actions+Orderings: " << numOrderingAndActionVars << endl;
            actionCost = numOrderingAndActionVars - numActions + 1;
            hardClauseCost = (numActions + 1) * actionCost + 1;

            unsigned long long int numClauses = 0;

            ofstream file(filename);
            if (!file)
            {
                cerr << "Error: Could not open file." << std::endl;
                return;
            }

            file << pad_string_to_32_bytes("Hello There");

            file << "c Paper Soft-Clauses Actions (9), and paper (1), and layering" << endl;
            for (int step = 0; step < numSteps; step++)
            {
                for (pair<int, int> rAPair : stepToActionsVarReal[step])
                {
                    // paper (9)
                    addNegatedAction(file, rAPair.first);
                    // paper (1)
                    addHardClauseNeg(file, orderingArray[rAPair.first][rAPair.first]);
                    // layering
                    addHardClauseFirstNegSecTrue(file, rAPair.first, orderingArray[artificiallyActionsBeforeStep[step].second][rAPair.first]);
                    addHardClauseFirstNegSecTrue(file, rAPair.first, orderingArray[rAPair.first][artificiallyActionsBeforeStep[step + 1].first]);
                    numClauses += 4;
                }
            }

            // force intermediate Actions to appear (2)
            file << "c Paper 2, force intermediate Actions" << endl;
            for (int step = 0; step < numSteps + 1; step++)
            {
                pair<int, int> rAPair = artificiallyActionsBeforeStep[step];
                addHardClause(file, rAPair.first);
                addHardClause(file, rAPair.second);
                // paper (4) optimized
                addHardClause(file, orderingArray[rAPair.first][rAPair.second]);
                numClauses += 3;
                if (step < numSteps)
                {
                    addHardClause(file, orderingArray[rAPair.second][artificiallyActionsBeforeStep[step + 1].first]);
                    numClauses++;
                }
            }

            // paper (3) and minimize orderings (8)
            file << "c Paper 3, Soft-Clauses Orderings" << endl;
            for (int a1 = 1; a1 <= numActions; a1++)
            {
                for (int a2 = 1; a2 <= numActions; a2++)
                {
                    if (orderingArray[a1][a2] != -1)
                    {
                        addHardClauseFirstNegSecTrue(file, orderingArray[a1][a2], a1); // Paper (3)
                        addHardClauseFirstNegSecTrue(file, orderingArray[a1][a2], a2); // Paper (3)
                        // addNegatedOrdering(file, orderingArray[a1][a2]);
                        // numClauses = numClauses + 3;
                        numClauses = numClauses + 2;
                    }
                }
            }

            timeval tp;
            gettimeofday(&tp, NULL);
            long startT = tp.tv_sec * 1000 + tp.tv_usec / 1000;

            // paper (5)
            file << "c Paper 5" << endl;
            for (int a1 = 1; a1 <= numActions; a1++)
            {
                for (int a2 = 1; a2 <= numActions; a2++)
                {
                    if ((a1 == a2) || (orderingArray[a1][a2] == -1))
                    {
                        continue;
                    }

                    for (int a3 = 1; a3 <= numActions; a3++)
                    {
                        if ((a2 == a3) || (orderingArray[a2][a3] == -1))
                        {
                            continue;
                        }
                        addHardClauseTwoNegOneTrue(file, orderingArray[a1][a2], orderingArray[a2][a3], orderingArray[a1][a3]);
                        numClauses = numClauses + 1;
                    }
                }
            }
            gettimeofday(&tp, NULL);
            long currentT = tp.tv_sec * 1000 + tp.tv_usec / 1000;
            getNumTime = getNumTime + currentT - startT;

            // Skip encoding 6, by only considering adders after the last intermediate task deleting prec before action
            for (int outerStep = 0; outerStep < numSteps + 1; outerStep++)
            {
                for (int prec : precsArtificial[outerStep])
                {
                    vector<int> possibleAdders;
                    int firstStepAdders = getLastDeletionUpToStep(prec, outerStep);
                    if (firstStepAdders == 0)
                    {
                        if (findIntInVector(initalActionAdds, prec))
                        {
                            possibleAdders.push_back(1);
                        }
                    }
                    else if (firstStepAdders == outerStep)
                    {
                        addHardClauseNeg(file, artificiallyActionsBeforeStep[outerStep].second);
                        numClauses++;
                        return;
                    }
                    for (int innerStep = firstStepAdders; innerStep < outerStep; innerStep++)
                    {
                        for (pair<int, int> rAPair : stepToActionsVarReal[innerStep])
                        {
                            if (varInAddOfAction(prec, rAPair.second))
                            {
                                possibleAdders.push_back(rAPair.first);
                            }
                        }
                    }
                    addHardClauseFirstNegVectorTrue(file, artificiallyActionsBeforeStep[outerStep].second, possibleAdders);
                    numClauses++;
                    possibleAdders.clear();
                }
                if (outerStep == numSteps)
                {
                    continue;
                }
                for (pair<int, int> rAPair : stepToActionsVarReal[outerStep])
                {
                    if (htn->numPrecs[rAPair.second] == 0)
                    {
                        continue;
                    }
                    for (int precIndex = 0; precIndex < htn->numPrecs[rAPair.second]; precIndex++)
                    {
                        int prec = htn->precLists[rAPair.second][precIndex];
                        vector<int> possibleAdders;
                        int firstStepAdders = getLastDeletionUpToStep(prec, outerStep);
                        if (firstStepAdders == 0)
                        {
                            if (findIntInVector(initalActionAdds, prec))
                            {
                                possibleAdders.push_back(1);
                            }
                        }
                        for (int innerStep = firstStepAdders; innerStep <= outerStep; innerStep++)
                        {
                            for (pair<int, int> rAPair2 : stepToActionsVarReal[innerStep])
                            {
                                if (varInAddOfAction(prec, rAPair2.second))
                                {
                                    possibleAdders.push_back(rAPair2.first);
                                }
                            }
                        }
                        addHardClauseFirstNegVectorTrue(file, rAPair.first, possibleAdders);
                        numClauses++;
                        possibleAdders.clear();
                    }
                }
            }

            file.close();
            adapt(numOrderingAndActionVars, numClauses, hardClauseCost, filename);

            cout << "Num Clauses: " << numClauses << endl;

            // delete
            initalActionAdds.clear();
            artificiallyActionsBeforeStep.clear();
            for (auto &innerVector : stepToActionsVarReal)
            {
                innerVector.clear();
            }
            stepToActionsVarReal.clear();
            for (auto &innerVector : precsArtificial)
            {
                innerVector.clear();
            }
            precsArtificial.clear();
            for (auto &innerVector : delsArtificial)
            {
                innerVector.clear();
            }
            delsArtificial.clear();

            for (int a = 1; a <= numActions; a++)
            {
                delete[] orderingArray[a];
            }
            delete[] orderingArray;
        }

    public:
        long buildTime = 0;
        long calcTime = 0;
        long getNumTime = 0;

        satHeuristic(Model *htnModel, int index) : Heuristic(htnModel, index)
        {
            htn = htnModel;
        }

        string getDescription()
        {
            return "satHeuristic";
        }

        void setHeuristicValue(searchNode *n, searchNode *parent, int action) override
        {
            setHeuristicValue(n, parent);
        }

        void setHeuristicValue(searchNode *n, searchNode *parent, int absTask, int method) override
        {
            setHeuristicValue(n, parent);
        }

        void setHeuristicValue(searchNode *n, searchNode *parent)
        {
            if (n->numAbstract == 0 && n->numPrimitive == 0)
            {
                n->heuristicValue[index] = 0;
                return;
            }

            timeval tp;
            gettimeofday(&tp, NULL);
            long startT = tp.tv_sec * 1000 + tp.tv_usec / 1000;

            makeSATFile("../RamDisk/SatFile.wcnf", n);

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
        };
    };
}