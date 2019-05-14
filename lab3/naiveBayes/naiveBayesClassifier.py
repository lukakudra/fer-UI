import util
import math


class NaiveBayesClassifier(object):
    """
    See the project description for the specifications of the Naive Bayes classifier.

    Note that the variable 'datum' in this code refers to a counter of features
    (not to a raw samples.Datum).
    """

    def __init__(self, legalLabels, smoothing=0, logTransform=False, featureValues=util.Counter()):
        self.legalLabels = legalLabels
        self.type = "naivebayes"
        # this is the smoothing parameter, ** use it in your train method **
        self.k = int(smoothing)
        self.logTransform = logTransform
        self.featureValues = featureValues  # empty if there is no smoothing

    def fit(self, trainingData, trainingLabels):
        """
        Trains the classifier by collecting counts over the training data, and
        stores the Laplace smoothed estimates so that they can be used to classify.

        trainingData is a list of feature dictionaries.  The corresponding
        label lists contain the correct label for each instance.

        To get the list of all possible features or labels, use self.features and self.legalLabels.
        """

        # the names of the features in the dataset
        self.features = trainingData[0].keys()

        self.prior = util.Counter()  # probability over labels
        # Conditional probability of feature feat for a given class having value v
        self.conditionalProb = util.Counter()
        # HINT: could be indexed by (feat, label, value)

        # TODO:
        # construct (and store) the normalized smoothed priors and conditional probabilities

        "*** YOUR CODE HERE ***"

        hypothesisCounter = util.Counter()
        valueCounter = util.Counter()
        lengthOfData = len(trainingData)

        for i in range(0, lengthOfData):
            feature = trainingData[i]
            label = trainingLabels[i]
            self.prior[label] += 1
            hypothesisCounter[label] += 1
            for key, value in feature.iteritems():
                self.conditionalProb[key, label, value] += 1
                valueCounter[value] += 1

        for key, value in self.prior.iteritems():
            self.prior[key] = (value + self.k * 1) / \
                (float(lengthOfData) + len(self.prior) * self.k)

        for key, value in self.conditionalProb.iteritems():
            nHypothesis = hypothesisCounter[key[1]]
            nValue = len(valueCounter)
            self.conditionalProb[key] = (
                value + self.k * 1) / (float(nHypothesis) + nValue * self.k)

    def predict(self, testData):
        """
        Classify the data based on the posterior distribution over labels.

        You shouldn't modify this method.
        """

        guesses = []
        # posterior probabilities are stored for later data analysis.
        self.posteriors = []

        for instance in testData:
            if self.logTransform:
                posterior = self.calculateLogJointProbabilities(instance)
            else:
                posterior = self.calculateJointProbabilities(instance)
            guesses.append(posterior.argMax())
            self.posteriors.append(posterior)
        return guesses

    def calculateJointProbabilities(self, instance):
        """
        Returns the joint distribution over legal labels and the instance.
        Each probability should be stored in the joint counter, e.g.
        Joint[3] = <Estimate of ( P(Label = 3, instance) )>

        To get the list of all possible features or labels, use self.features and
        self.legalLabels.
        """
        joint = util.Counter()

        for label in self.legalLabels:
            # calculate the joint probabilities for each class
            "*** YOUR CODE HERE ***"
            produkt = 1
            for key, value in instance.iteritems():
                produkt *= self.conditionalProb[(key, label, value)]

            joint[label] = self.prior[label] * produkt

        return joint

    def calculateLogJointProbabilities(self, instance):
        """
        Returns the log-joint distribution over legal labels and the instance.
        Each log-probability should be stored in the log-joint counter, e.g.
        logJoint[3] = <Estimate of log( P(Label = 3, instance) )>

        To get the list of all possible features or labels, use self.features and
        self.legalLabels.
        """
        logJoint = util.Counter()

        for label in self.legalLabels:
            # calculate the log joint probabilities for each class
            "*** YOUR CODE HERE ***"
            suma = 0
            for key, value in instance.iteritems():
                suma += math.log(self.conditionalProb[(key, label, value)])

            logJoint[label] = math.log(self.prior[label]) + suma

        return logJoint
